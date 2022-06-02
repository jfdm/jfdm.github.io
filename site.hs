{-# LANGUAGE OverloadedStrings #-}
--  ---------------------------------------------------------------- [ site.hs ]
--  Module    : site.hs
--  Copyright : (c) Jan de Muijnck-Hughes
--  License   : see LICENSE
--  -------------------------------------------------------------------- [ EOH ]

import            Data.Maybe                      (fromMaybe, listToMaybe)
import            Data.Either                     (fromRight)
import            Data.Monoid                     ((<>), mconcat)
import            Data.Functor                    ((<$>), fmap)
import            Data.Char                       (isSpace, toLower, toUpper)
import            Data.List                       (intercalate, intersperse, foldl', isPrefixOf)
import            Data.Text                       (pack)
import            Control.Applicative             ((<|>), Alternative(..))
import            Control.Monad                   (msum, filterM, (<=<), liftM, filterM)
import            Control.Monad.Fail              (MonadFail)
import            System.Environment              (getArgs)
import            Text.Blaze.Html                 (toHtml, toValue, (!))
import            Text.Blaze.Html5.Attributes     (href, class_)
import            Text.Blaze.Html.Renderer.String (renderHtml)

import qualified  Text.Blaze.Html5                as H
import            Text.Pandoc.Options
import            Text.Pandoc.Templates
import            Text.Pandoc.Class

import Control.Applicative
import Control.Arrow
import Control.Monad
import            Data.Either                     (fromRight)
import            Data.Text                       (pack)
import Data.Default           (def)
import Data.Maybe (fromJust)
import Data.Monoid (mappend)
import            Text.Blaze.Html.Renderer.String (renderHtml)
import           Text.Pandoc.Options            ( WriterOptions
                                                , writerNumberSections
                                                , writerSyntaxMap
                                                , writerTOCDepth
                                                , writerTableOfContents
                                                , writerTemplate
                                                )
import            Text.Blaze.Html                 (toHtml, toValue, (!))
import            Text.Blaze.Html5.Attributes     (href, class_)
import            Text.Blaze.Html.Renderer.String (renderHtml)
import qualified  Text.Blaze.Html5                as H
import Hakyll
import            Text.Pandoc.Options
import            Text.Pandoc.Templates
import Debug.Trace

{-
https://svejcar.dev/posts/2019/11/27/table-of-contents-in-hakyll/
https://argumatronic.com/posts/2018-01-16-pandoc-toc.html
https://gisli.hamstur.is/2020/08/my-personal-hakyll-cheatsheet/
-}
--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do
    match "images/*" $ do
        route   idRoute
        compile copyFileCompiler

    match "css/*" $ do
        route   idRoute
        compile compressCssCompiler

    match "js/*" $ do
        route   idRoute
        compile compressCssCompiler

    match "*.bib" $ compile biblioCompiler
    match "*.csl" $ compile cslCompiler

    match "draft/*" $ do
        route   idRoute
        compile copyFileCompiler


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
      compile $ blogCompiler -- pandocBiblioCompiler "style.csl" "biblio.bib"
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

    match "talks.md" $ do
      route   $ setExtension "html"
      compile $ pandocBiblioCompiler "fullcite.csl" "talks.bib"
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls


    match "publications.md" $ do
      route   $ setExtension "html"
      compile $ pandocBiblioCompiler "fullcite.csl" "publications.bib"
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls

    match "research.md" $ do
      route   $ setExtension "html"
      compile $ pandocBiblioCompiler "fullcite.csl" "software.bib"
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls

    match "index.md" $ do
      route   $ setExtension "html"
      compile $ do
            posts <- recentFirst =<< loadAll "post/*"
            let indexCtx =
                    listField "posts" postCtx (return $ take 5 posts) `mappend`
                    defaultContext

            pandocCompiler
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/default.html" indexCtx
                >>= relativizeUrls

    match "*.md" $ do
      route   $ setExtension "html"
      compile $ pandocCompiler
            >>= applyAsTemplate defaultContext
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
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

blogCompiler :: Compiler (Item String)
blogCompiler = do
   ident <- getUnderlying
   toc   <- getMetadataField ident "withtoc"
   pandocCompilerWith defaultHakyllReaderOptions (maybe defaultOptions blogOptions toc)
   where
      defaultOptions = defaultHakyllWriterOptions
      blogOptions = const blogWriterOptions

blogWriterOptions :: WriterOptions
blogWriterOptions =
   defaultHakyllWriterOptions
      {

        writerTableOfContents = True
      , writerNumberSections  = True
      , writerTOCDepth        = 1
      , writerTemplate        =
         let
            toc = "$toc$" :: String
            body = "$body$" :: String
            html = pack . renderHtml $ do
                     H.div ! class_ "toc" $ do
                        toHtml toc
                     toHtml body
            template  =  fromRight mempty <$> compileTemplate "" html
            runPureWithDefaultPartials = runPure . runWithDefaultPartials
            eitherToMaybe = either (const Nothing) Just
         in
            eitherToMaybe (runPureWithDefaultPartials template)
   }
