.PHONY: all verify go rust clean bench bench-go bench-rust compare

BOLD_CYAN := \033[1;36m
RESET := \033[0m

define log
	@printf '$(BOLD_CYAN)[%s]$(RESET)\n' "$(1)"
endef

DAFNY := dafny
GO    := go
CARGO := cargo
NAME  := drb
CORES := $(shell nproc)

BUILD_DIR := build
DFY_OUT   := $(BUILD_DIR)/src

# Go: Dafny appends "-go"
GO_SRC  := $(DFY_OUT)-go/src

# Rust: Dafny appends "-rust"
RUST_SRC := $(DFY_OUT)-rust

DFY_SRCS := $(wildcard *.dfy)

BENCH_GO_SRC   := bench/go/bench_test.go
BENCH_RUST_SRC := bench/rust/rbt_bench.rs
BENCH_GO_DIR   := $(DFY_OUT)-go/src/bench
BENCH_RUST_DIR := $(RUST_SRC)/benches

all: verify go rust

verify:
	@$(call log,Verifying Dafny proofs)
	@$(DAFNY) verify --cores $(CORES) --progress Batch $(DFY_SRCS)

# ── Go ────────────────────────────────────────────────────────────────────────

$(GO_SRC): $(DFY_SRCS)
	@$(call log,Translating Dafny to Go)
	@$(DAFNY) build --no-verify --target go --output $(DFY_OUT) $(DFY_SRCS)

go: $(GO_SRC)

# ── Rust ──────────────────────────────────────────────────────────────────────

$(RUST_SRC): $(DFY_SRCS)
	@$(call log,Translating Dafny to Rust)
	@$(DAFNY) build --no-verify --target rs --enforce-determinism --output $(DFY_OUT) $(DFY_SRCS)

rust: $(RUST_SRC)

# ── Benchmarks ───────────────────────────────────────────────────────────────

bench-go: $(GO_SRC)
	@$(call log,Running Go benchmarks)
	@mkdir -p $(BENCH_GO_DIR)
	@cp $(BENCH_GO_SRC) $(BENCH_GO_DIR)/bench_test.go
	@GOPATH=$(abspath $(DFY_OUT)-go) GO111MODULE=off \
		$(GO) test -bench=. -benchmem -benchtime=5s bench

bench-rust: $(RUST_SRC)
	@$(call log,Running Rust benchmarks)
	@mkdir -p $(BENCH_RUST_DIR)
	@cp $(BENCH_RUST_SRC) $(BENCH_RUST_DIR)/rbt_bench.rs
	@grep -q '^\[dev-dependencies\]' $(RUST_SRC)/Cargo.toml || printf '\n[dev-dependencies]\ncriterion = { version = "0.5", features = ["html_reports"] }\n\n[[bench]]\nname = "rbt_bench"\nharness = false\n' >> $(RUST_SRC)/Cargo.toml
	@$(CARGO) bench --manifest-path $(RUST_SRC)/Cargo.toml

bench-compare: $(GO_SRC) $(RUST_SRC)
	@$(call log,Running Go benchmarks)
	@mkdir -p $(BENCH_GO_DIR) $(BUILD_DIR)
	@cp $(BENCH_GO_SRC) $(BENCH_GO_DIR)/bench_test.go
	@GOPATH=$(abspath $(DFY_OUT)-go) GO111MODULE=off \
		$(GO) test -bench=. -benchtime=5s bench > $(BUILD_DIR)/bench-go.txt
	@$(call log,Running Rust benchmarks)
	@mkdir -p $(BENCH_RUST_DIR)
	@cp $(BENCH_RUST_SRC) $(BENCH_RUST_DIR)/rbt_bench.rs
	@grep -q '^\[dev-dependencies\]' $(RUST_SRC)/Cargo.toml || printf '\n[dev-dependencies]\ncriterion = { version = "0.5", features = ["html_reports"] }\n\n[[bench]]\nname = "rbt_bench"\nharness = false\n' >> $(RUST_SRC)/Cargo.toml
	@$(CARGO) bench --manifest-path $(RUST_SRC)/Cargo.toml 2>/dev/null > $(BUILD_DIR)/bench-rust.txt
	@python3 bench/compare.py $(BUILD_DIR)/bench-go.txt $(BUILD_DIR)/bench-rust.txt

# ── Shared ────────────────────────────────────────────────────────────────────

clean:
	@$(call log,Cleaning build directory)
	@rm -rf $(BUILD_DIR)/
