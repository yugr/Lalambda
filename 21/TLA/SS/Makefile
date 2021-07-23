TESTS = web/SimpleMath/SimpleMath \
  web/HourClock/HourClock web/HourClock/HourClock2 \
  local/HourClock/HourClockInvalid local/HourClock/HourClock2Invalid \
  local/AsynchronousInterface/PrintValues local/AsynchronousInterface/HourClockChannel \
  local/FIFO/1/HourClockSender local/FIFO/2/HourClockSender local/FIFO/3/HourClock \
  local/MoreMath/PrintValues \
  local/TLC/MCPythagorean local/TLC/MCEssentialPythagorean

LOGS = $(TESTS:%=out/%.log)

all: $(LOGS)

out/%.log: %.tla
	mkdir -p `dirname $@`
	time ../tlc $^ 2>&1 | tee $@

clean:
	rm -rf out states

.PHONY: all clean
