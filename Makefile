# ----------------------------------------------------------------- [ Makefile ]
# Module    : Makefile
# Copyright : (c) Jan de Muijnck-Hughes
# License   : see LICENSE
# ---------------------------------------------------------------------- [ EOH ]

REPO := git@github.com:jfdm/jfdm.github.io.git

.PHONY: build serve deploy clean

site-init: site.hs
	ghc --make -threaded site.hs

build: site-init
	./site build

clean:
	./site clean

serve:
	./site server

watch:
	./site watch

deploy:
	rm -rf _site/.git
	(cd _site; git init && git add .)
	(cd _site; git config user.email "")
	(cd _site; git config user.name None)
	(cd _site; git commit -m "Site Generated on `date`")
	(cd _site; git remote add origin ${REPO})
	(cd _site; git push -f origin master)
# ---------------------------------------------------------------------- [ EOF ]
