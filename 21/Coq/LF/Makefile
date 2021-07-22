SRCS = $(wildcard *.v)
LOGS = $(SRCS:.v=.log)

all: $(LOGS)

%.log: %.v
	coqtop -batch -l $^ > $@

clean:
	rm -f *.log

.PHONY: all clean
