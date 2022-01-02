.PHONY: test lint check

test:
	cargo test
	cargo build
	./test/test.sh
	./test/error.sh
	rm -rf ./_tmp

lint:
	cargo clippy -- -D warnings

check: lint test