{-# LANGUAGE OverloadedStrings #-}
--  ---------------------------------------------------------------- [ site.hs ]
--  Module    : site.hs
--  Copyright : (c) Jan de Muijnck-Hughes
--  License   : see LICENSE
--  -------------------------------------------------------------------- [ EOH ]

import Control.Applicative
import Control.Arrow
import Control.Monad

import Data.Default           (def)
import Data.Maybe (fromJust)
import Data.Monoid (mappend)

import Hakyll

import Debug.Trace

--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do
    match "images/*" $ do
        route   idRoute
        compile copyFileCompiler

    match "css/*" $ do
        route   idRoute
        compile compressCssCompiler

    match "*.bib" $ compile biblioCompiler
    match "*.csl" $ compile cslCompiler

--  ------------------------------------------------------------- [ Build Tags ]
    tags <- buildTags ("post/*") (fromCapture "tags/*.html")

    tagsRules tags $ \tag pattern -> do
      let title = "Posts tagged \"" ++ tag ++ "\""
      route idRoute
      compile $ do
        posts <- recentFirst =<< loadAll pattern
        let ctx = constField "title" title
                      `mappend` listField "posts" postCtx (return posts)
                      `mappend` defaultContext

        makeItem ""
                >>= loadAndApplyTemplate "templates/tag.html" ctx
                >>= loadAndApplyTemplate "templates/default.html" ctx
                >>= relativizeUrls

--  ------------------------------------------------------- [ Compile Patterns ]

    match "post/*.md" $ do
      route $ setExtension "html"
      compile $ bibtexCompiler "style.csl" "biblio.bib"
        >>= loadAndApplyTemplate "templates/post.html" (postCtxWithTags tags)
        >>= loadAndApplyTemplate "templates/default.html" (postCtxWithTags tags)
        >>= relativizeUrls

--  --------------------------------------------------------- [ Generate Lists ]

    create ["posts.html"] $ do
        route idRoute
        compile $ do
            ps <- recentFirst =<< loadAll "post/*"
            let archiveCtx =
                    listField "posts" postCtx (return ps) `mappend`
                    constField "title" "List o' Posts" `mappend`
                    defaultContext


            makeItem ""
                >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
                >>= loadAndApplyTemplate "templates/default.html" archiveCtx
                >>= relativizeUrls

--  ------------------------------------------------------------------ [ Index ]

    match "publications.md" $ do
      route   $ setExtension "html"
      compile $ bibtexCompiler "fullcite.csl" "publications.bib"
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls

    match "software.md" $ do
      route   $ setExtension "html"
      compile $ bibtexCompiler "fullcite.csl" "software.bib"
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls

--    match "*.md" $ do
--      route   $ setExtension "html"
--      compile $ pandocCompiler
--            >>= applyAsTemplate defaultContext
--            >>= loadAndApplyTemplate "templates/default.html" defaultContext
--            >>= relativizeUrls

    match "contact.md" $ do
      route   $ setExtension "html"
      compile $ pandocCompiler
            >>= applyAsTemplate defaultContext
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls

    match "teaching.md" $ do
      route   $ setExtension "html"
      compile $ pandocCompiler
            >>= applyAsTemplate defaultContext
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls


    match "index.html" $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll "post/*"
            let indexCtx =
                    listField "posts" postCtx (return posts) `mappend`
                    defaultContext

            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/default.html" indexCtx
                >>= relativizeUrls

    match "templates/*" $ compile templateCompiler


--  --------------------------------------------------------------- [ Contexts ]

postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" `mappend`
    defaultContext

postCtxWithTags :: Tags -> Context String
postCtxWithTags tags = tagsField "tags" tags `mappend` postCtx


bibtexCompiler :: String -> String -> Compiler (Item String)
bibtexCompiler cslFileName bibFileName = do
    csl <- load $ fromFilePath cslFileName
    bib <- load $ fromFilePath bibFileName
    liftM writePandoc
        (getResourceBody >>= readPandocBiblio def csl bib)

--  -------------------------------------------------------------------- [ EOF ]
