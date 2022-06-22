R := Rscript -e
bookdown = $(R) "bookdown::render_book('_bookdown.yml', 'bookdown::$(1)')"

SRC := $(CURDIR)/src
MAIN := $(SRC)/index.agda
OUT := $(CURDIR)/_book

.PHONY: all test pdf html
# pdf must be before html in order to create pdf download button
all: pdf html

test:
	cd "$(SRC)"; agda "$(MAIN)"

pdf:
	$(call bookdown,pdf_book)

html: TMP := "$(shell mktemp -d)"
html: TMP_SRC := "$(TMP)/$(notdir $(SRC))"
html: TMP_OUT := "$(TMP)/$(notdir $(OUT))"
html:
	@mkdir -p "$(TMP_SRC)"
	@mkdir -p "$(TMP_OUT)"
# generate md and html files with agda syntax highlighting
	cd "$(SRC)"; agda --html --html-highlight=auto --html-dir="$(TMP_SRC)" "$(MAIN)"
# agda css must have precedence
	@chmod +w "$(TMP_SRC)/"*.css
	@sed -i 's/\(;\? *}\|;\)/ !important\1/' "$(TMP_SRC)/"*.css
# copy required configuration files
	@cp *.{yml,md,Rmd,bib,csl} "$(TMP)/"
	@sed -i 's/\.lagda//' "$(TMP)/"*.yml
	@cp "$(OUT)/"*.pdf "$(TMP_OUT)"
# execute bookdown
	cd "$(TMP)"; $(call bookdown,gitbook)
# copy to destination folder
	@cp "$(TMP_SRC)/"*.{html,css} "$(OUT)/"
	@cp -r "$(TMP_OUT)" "$(dir $(OUT))/"
	@rm -rf "$(TMP)"

.PHONY: clean
clean:
	rm -rf "$(OUT)" _minted* *.pyg *.log

