{-# LANGUAGE OverloadedStrings #-}
--  ---------------------------------------------------------------- [ site.hs ]
--  Module    : site.hs
--  Copyright : (c) Jan de Muijnck-Hughes
--  License   : see LICENSE
--  -------------------------------------------------------------------- [ EOH ]

import Control.Applicative
import Control.Arrow
import Control.Monad

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

--  ------------------------------------------------------------- [ Build Tags ]
    tags <- buildTags ("post") (fromCapture "tags/*.html")

    tagsRules tags $ \tag pattern -> do
      let title = "Posts tagged \"" ++ tag ++ "\""
      route idRoute
      compile $ do
        posts <- recentFirst =<< loadAll "post/*"
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
      compile $ pandocCompiler
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

    match "*.md" $ do
      route $ setExtension "html"
      compile $ pandocCompiler
        >>= loadAndApplyTemplate "templates/default.html" (postCtxWithTags tags)
        >>= relativizeUrls

    match "software.html" $ do
        route idRoute
        compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/default.html" defaultContext


    match "index.html" $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll "post/*"
            let indexCtx =
                    listField "posts" postCtx (return posts) `mappend`
                    constField "title" "Home"                `mappend`
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


--  -------------------------------------------------------------------- [ EOF ]
