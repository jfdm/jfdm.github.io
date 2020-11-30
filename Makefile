# ----------------------------------------------------------------- [ Makefile ]
# Module    : Makefile
# Copyright : (c) Jan de Muijnck-Hughes
# License   : see LICENSE
# ---------------------------------------------------------------------- [ EOH ]

REPO := git@github.com:jfdm/jfdm.github.io.git

SITE := stack exec site

.PHONY: build serve deploy clean watch

config:
	stack build

build: config
	${SITE} build

clean: config
	${SITE} clean

serve: config
	${SITE} server

watch: config
	${SITE} watch

deploy: config build
	rm -rf _site/.git
	(cd _site; git init && git add .)
#	(cd _site; git config user.email "")
#	(cd _site; git config user.name None)
	(cd _site; git commit -m "Site Generated on `date`")
	(cd _site; git remote add origin ${REPO})
	(cd _site; git push -f origin master)
# ---------------------------------------------------------------------- [ EOF ]
