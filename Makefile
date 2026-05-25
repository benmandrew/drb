.PHONY: all verify dafny rust clean

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

all: verify $(BINARY)

verify:
	@$(call log,Verifying Dafny proofs)
	@$(DAFNY) verify --cores $(CORES) --progress Batch $(DFY_SRCS)

# ── Go ────────────────────────────────────────────────────────────────────────

$(GO_SRC): $(DFY_SRCS)
	@$(call log,Compiling Dafny to Go source)
	@$(DAFNY) build --no-verify --target go --output $(DFY_OUT) $(DFY_SRCS)

dafny: $(GO_SRC)

# Dafny emits GOPATH-style imports, so use GOPATH mode (GO111MODULE=off)
$(BINARY): $(GO_SRC)
	@mkdir -p $(BUILD_DIR)
	@$(call log,Compiling Go source)
	@GOPATH=$(abspath $(DFY_OUT)-go) GO111MODULE=off \
		$(GO) build -C $(abspath $(GO_SRC)) -o $(abspath $(BINARY)) .

# ── Rust ──────────────────────────────────────────────────────────────────────

$(RUST_SRC): $(DFY_SRCS)
	@$(call log,Compiling Dafny to Rust source)
	@$(DAFNY) build --no-verify --target rs --enforce-determinism --output $(DFY_OUT) $(DFY_SRCS)

$(RUST_BINARY): $(RUST_SRC)
	@$(call log,Compiling Rust source)
	@$(CARGO) build --release --manifest-path $(RUST_SRC)/Cargo.toml
	@cp $(RUST_SRC)/target/release/src $@

rust: $(RUST_BINARY)

# ── Shared ────────────────────────────────────────────────────────────────────

clean:
	@$(call log,Cleaning build directory)
	@rm -rf $(BUILD_DIR)/
