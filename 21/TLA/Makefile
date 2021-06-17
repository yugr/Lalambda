TESTS = web/SimpleMath/SimpleMath \
  web/HourClock/HourClock web/HourClock/HourClock2 \
  local/HourClock/HourClockInvalid local/HourClock/HourClock2Invalid \
  local/AsynchronousInterface/PrintValues local/AsynchronousInterface/HourClockChannel

LOGS = $(TESTS:%=out/%.log)

all: $(LOGS)

out/%.log: %.tla %.cfg
	mkdir -p `dirname $@`
	./tlc $^ 2>&1 | tee $@

clean:
	rm -rf out

.PHONY: all clean
