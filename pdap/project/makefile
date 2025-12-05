CC      = smpicc
CFLAGS  = -Wall -Wextra -g # -fsanitize=address

SRCS    := $(wildcard *.c)
HEADERS := $(wildcard *.h)
TARGET  := main

all: $(TARGET)

$(TARGET): $(SRCS) $(HEADERS)
	$(CC) $(CFLAGS) -o $@ max_flow-skeleton.c

.PHONY: format
format:
	find . -name "*.c" -o -name "*.h" | xargs clang-format -i
	find . -name "*.py" | xargs yapf -i --parallel --style='{based_on_style: google, indent_width: 2}'

.PHONY: clean
clean:
	rm -rf $(TARGET) $(TARGET).dSYM

.PHONY: clean-tests
clean-tests: clean
	rm -rf tests

.PHONY: clean-benchs
clean-benchs: clean
	rm -rf benchs

.PHONY: clean-smpi
clean-smpi: clean
	rm -rf platforms hostfiles

.PHONY: clean-figures
clean-figures: clean
	rm -rf figures

.PHONY: clean-results
clean-results: clean
	rm bench_results*.csv


.PHONY: clean-full
clean-full: clean clean-tests clean-benchs clean-smpi clean-results clean-figures

.PHONY: test
test: $(TARGET)
	mkdir -p platforms
	mkdir -p hostfiles
	mkdir -p tests
	ipython test_flow.py

.PHONY: test-regenerate
test-regenerate: $(TARGET) clean-tests
	mkdir -p platforms
	mkdir -p hostfiles
	mkdir -p tests
	ipython test_flow.py


.PHONY: bench
bench: $(TARGET)
	mkdir -p platforms
	mkdir -p hostfiles
	mkdir -p benchs
	ipython bench_flow.py

.PHONY: bench-regenerate
bench-regenerate: $(TARGET) clean-benchs
	mkdir -p platforms
	mkdir -p hostfiles
	mkdir -p benchs
	ipython bench_flow.py


.PHONY: bench-regenerate
tar:
	tar cvfz salou-hugo.tar.gz max_flow*.c report.pdf *.py *.ttf .clang-format makefile
	@echo "Created salou-hugo.tar.gz"
