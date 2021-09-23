ISABELLE=/opt/Isabelle2021/bin/isabelle

outline.pdf : $(wildcard *.thy) document/root.tex document/localvars.aux document/qrhl.aux ROOT
	$(ISABELLE) build -D .

document/localvars.aux : ../local-vars-qrhl/localvars.aux
	cp -va $^ document/

document/qrhl.aux :
	cd document && git archive --remote=git@gitlab.com:unruh/qrhl-paper.git arxiv-v2 qrhl.aux | tar -x

cloc :
	cloc --read-lang-def cloc-lang-def --out=/dev/stdout *.thy
