R := Rscript -e
bookdown = $(R) "bookdown::render_book('_bookdown.yml', 'bookdown::$(1)')"


.PHONY: all
all: pdf epub html agda_html

html:
	$(call bookdown,gitbook)

pdf:
	$(call bookdown,pdf_book)

epub:
	$(call bookdown,epub_book)
	
agda_html:
	agda --html --html-dir=_code ci.lagda.md 


.PHONY: clean
clean:
	rm -rf _book _code

