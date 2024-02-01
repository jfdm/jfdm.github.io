# ----------------------------------------------------------------- [ Makefile ]
# Module    : Makefile
# Copyright : (c) Jan de Muijnck-Hughes
# License   : see LICENSE
# ---------------------------------------------------------------------- [ EOH ]

REPO := git@github.com:jfdm/jfdm.github.io.git

#SITE := stack exec site

.PHONY: build serve deploy clean

build:
	hugo --minify

clean:
	rm -rf public_html

serve:
	hugo server

deploy: clean build
	(cd public_html; echo tyde.systems > CNAME)
	(cd public_html; git init && git add .)
#	(cd public_html; git config user.email "")
#	(cd public_html; git config user.name None)
	(cd public_html; git commit -m "Site Generated on `date`")
#	(cd public_html; git branch -m master main)
	(cd public_html; git remote add origin ${REPO})
	(cd public_html; git push -f origin main)
# ---------------------------------------------------------------------- [ EOF ]
