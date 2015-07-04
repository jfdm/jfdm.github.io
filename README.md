# libPattern

Software Design Patterns are a software engineering technique to provide well-documented solutions to recurrent software engineering problems.
These solutions represent the tried & tested design choices made my domain experts and presents them in a digestable format for non-domain experts.
`libPattern` is a pattern repository that collates existing patterns collected from literature into a single easy to view place.

Future work will be to make the patterns in this repository accessible through an API and make the repository computable.

## Contributing.

PRs are welcome but please consult CONTRIBUTING.md for more information.

The original pattern authors will retain copyright for their published work, and please ensure that you provide linkage to the original source of the pattern.

## Construction

This repository is currently developed as a static website using [Haykll](http://jaspervdj.be/hakyll/), and published using [GitHub Pages](https://pages.github.com/) for Projects.

### Building

To build the website you need to install Hakyll:

```sh
cabal install hakyll
```

Then execute the `Makefile` command:

```sh
make build
```

The `Makefile` is a simple overlay for many Hakyll commands.

### Deployment

Deployment of `libPattern` is achieved with the following `Makefile` command:

```sh
make deploy
```

This command builds the static site in `_site` and moves it to the `gh-pages` branch which github uses to publish the site.

Please note only those with a commit bit will be allowed to push to the site.

## References

Useful references for building and deploying with Hakyll and gh-pages include:

+ http://www.srid.ca/posts/2015-04-24-hakyll-and-circleci.html
+ http://jaspervdj.be/hakyll/
