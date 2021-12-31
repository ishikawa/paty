.PHONY = test lint check

test:
	cargo test
	cargo build
	./test.sh
	rm -f ./tmp*

lint:
	cargo clippy -- -D warnings

check: lint test