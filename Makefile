.PHONY: all verify dafny rust clean bench bench-go bench-rust compare

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

# Go: Dafny appends "-go", binary uses GOPATH mode
GO_SRC  := $(DFY_OUT)-go/src
BINARY  := $(BUILD_DIR)/$(NAME)

# Rust: Dafny appends "-rust", binary built via Cargo
RUST_SRC    := $(DFY_OUT)-rust
RUST_BINARY := $(BUILD_DIR)/$(NAME)-rs

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
	@$(call log,Compiling Dafny to Go source)
	@$(DAFNY) build --no-verify --target go --output $(DFY_OUT) $(DFY_SRCS)

# Dafny emits GOPATH-style imports, so use GOPATH mode (GO111MODULE=off)
$(BINARY): $(GO_SRC)
	@mkdir -p $(BUILD_DIR)
	@$(call log,Compiling Go source)
	@GOPATH=$(abspath $(DFY_OUT)-go) GO111MODULE=off \
		$(GO) build -C $(abspath $(GO_SRC)) -o $(abspath $(BINARY)) .

go: $(GO_SRC)

# ── Rust ──────────────────────────────────────────────────────────────────────

$(RUST_SRC): $(DFY_SRCS)
	@$(call log,Compiling Dafny to Rust source)
	@$(DAFNY) build --no-verify --target rs --enforce-determinism --output $(DFY_OUT) $(DFY_SRCS)

$(RUST_BINARY): $(RUST_SRC)
	@$(call log,Compiling Rust source)
	@$(CARGO) build --release --manifest-path $(RUST_SRC)/Cargo.toml
	@cp $(RUST_SRC)/target/release/src $@

rust: $(RUST_BINARY)

# ── Benchmarks ───────────────────────────────────────────────────────────────

bench-go: $(GO_SRC)
	@$(call log,Running Go benchmarks)
	@mkdir -p $(BENCH_GO_DIR)
	@cp $(BENCH_GO_SRC) $(BENCH_GO_DIR)/bench_test.go
	@GOPATH=$(abspath $(DFY_OUT)-go) GO111MODULE=off \
		$(GO) test -bench=. -benchmem -benchtime=5s bench

bench-rust: $(RUST_SRC)
	@$(call log,Patching Rust crate for benchmarks)
	@mkdir -p $(BENCH_RUST_DIR)
	@cp $(BENCH_RUST_SRC) $(BENCH_RUST_DIR)/rbt_bench.rs
	@grep -q '^\[lib\]' $(RUST_SRC)/Cargo.toml || printf '\n[lib]\nname = "src"\npath = "src/src.rs"\n\n[dev-dependencies]\ncriterion = { version = "0.5", features = ["html_reports"] }\n\n[[bench]]\nname = "rbt_bench"\nharness = false\n' >> $(RUST_SRC)/Cargo.toml
	@$(call log,Running Rust benchmarks)
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
	@grep -q '^\[lib\]' $(RUST_SRC)/Cargo.toml || printf '\n[lib]\nname = "src"\npath = "src/src.rs"\n\n[dev-dependencies]\ncriterion = { version = "0.5", features = ["html_reports"] }\n\n[[bench]]\nname = "rbt_bench"\nharness = false\n' >> $(RUST_SRC)/Cargo.toml
	@$(CARGO) bench --manifest-path $(RUST_SRC)/Cargo.toml 2>/dev/null > $(BUILD_DIR)/bench-rust.txt
	@python3 bench/compare.py $(BUILD_DIR)/bench-go.txt $(BUILD_DIR)/bench-rust.txt

# ── Shared ────────────────────────────────────────────────────────────────────

clean:
	@$(call log,Cleaning build directory)
	@rm -rf $(BUILD_DIR)/
