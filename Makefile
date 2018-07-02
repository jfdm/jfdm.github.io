# ----------------------------------------------------------------- [ Makefile ]
# Module    : Makefile
# Copyright : (c) Jan de Muijnck-Hughes
# License   : see LICENSE
# ---------------------------------------------------------------------- [ EOH ]

REPO := git@github.com:jfdm/jfdm.github.io.git

SITE := stack exec site

.PHONY: build serve deploy clean

config:
	stack build
build:
	${SITE} build

clean:
	${SITE} clean

serve:
	${SITE} server

watch:
	${SITE} watch


deploy:
	rm -rf _site/.git
	(cd _site; git init && git add .)
#	(cd _site; git config user.email "")
#	(cd _site; git config user.name None)
	(cd _site; git commit -m "Site Generated on `date`")
	(cd _site; git remote add origin ${REPO})
	(cd _site; git push -f origin master)
# ---------------------------------------------------------------------- [ EOF ]
