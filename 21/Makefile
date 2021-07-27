all: talk.pdf soc-team.pdf

%.pdf: %.md
	# Install marp from https://github.com/marp-team/marp-cli/releases
	marp --pdf $<

clean:
	rm -f *.pdf

.PHONY: clean all
