# TTNTEX=tutor-notes.tex
# TTNPDF=tutor-notes.pdf
SLTNTEX=soltn.tex
SLTNPDF=soltn.pdf

MDTOTEX=pandoc -f markdown -t latex

LECTMD=transscr.md
LECTTEX=transscr.tex
LECTPDF=transscr.pdf

TEXC=xelatex_halt-on-error


all: preproc solutions # $(LECTPDF)
.PHONY: all

SUBMAKES=$(wildcard ex*/Makefile)
preproc:
	for mkf in $(SUBMAKES) ; do \
            $(MAKE) -C $$(dirname $$mkf) ; \
          done
.PHONY: preproc


solutions: $(foreach dir, $(wildcard ex*), $(dir)/$(SLTNPDF))
.PHONY: solutions

lectures: $(foreach dir, $(wildcard lect*), $(dir)/$(LECTTEX))

# tutornotes: ex02/$(TTNPDF) ex04/$(TTNPDF) ex05/$(TTNPDF) ex06/$(TTNPDF) ex07/$(TTNPDF) ex08/$(TTNPDF) ex09/$(TTNPDF)
.PHONY: tutornotes


ex%/$(SLTNPDF): ex%/$(SLTNTEX) def-header-exerc.tex Makefile
	sh -c 'sed "s/\\\\theSheetNo/$*/g;s/\\\\catsubtitle//g" def-header-exerc.tex; sed "s/^ *\\\\\]/\\\\end{dmath\\*}/;s/^ *\\\\\[/\\\\begin{dmath\\*}/" $<; echo "\\end{document}"' > $<-full.tex
	$(TEXC) $<-full.tex
	rm $<-full.tex
	mv $(SLTNTEX)-full.pdf $@
	rm $(SLTNTEX)-full.aux

lect%/$(LECTTEX): lect%/$(LECTMD) def-header-lect.tex Makefile
	sh -c 'echo "\\\chapter{Lecture $*}"; $(MDTOTEX) $< | sed "s/\\\\\]/\\\\end{dmath\\*}/;s/\\\\\[/\\\\begin{dmath\\*}/"' > $@

$(LECTPDF): lectures
	sh -c 'cat def-header-lect.tex lect*/$(LECTTEX); echo "\\end{document}"' > $(LECTTEX)
	$(TEXC) $(LECTTEX)
# rm $(LECTTEX)


# ex%/$(TTNPDF): ex%/$(TTNTEX) default-header.tex Makefile
# 	sh -c 'sed "s/\\\\theSheetNo/$*/g;s/\\\\catsubtitle/Tutor notes/g" default-header.tex; sed "s/^\\\\\]/\\\\end{dmath\\*}/;s/^\\\\\[/\\\\begin{dmath\\*}/" $<; echo "\\end{document}"' > $<-full.tex
# 	$(TEXC) $<-full.tex
# 	rm $<-full.tex
# 	mv $(TTNTEX)-full.pdf $@
# 	rm $(TTNTEX)-full.aux
