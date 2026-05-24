.PHONY: all verify dafny clean

BOLD_CYAN := \033[1;36m
RESET := \033[0m

define log
	@printf '$(BOLD_CYAN)[%s]$(RESET)\n' "$(1)"
endef

DAFNY   := dafny
GO      := go
NAME    := drb

# Dafny appends "-go" to the --output path, so build/src → build/src-go
BUILD_DIR := build
DFY_OUT   := $(BUILD_DIR)/src
GO_SRC    := $(DFY_OUT)-go/src
BINARY    := $(BUILD_DIR)/$(NAME)

DFY_SRCS := $(wildcard *.dfy)

all: $(BINARY)

# Verify proofs without producing output
verify:
	@$(call log,Verifying Dafny proofs)
	$(DAFNY) verify $(DFY_SRCS)

# Compile Dafny → Go source
$(GO_SRC): $(DFY_SRCS)
	@$(call log,Compiling Dafny to Go source)
	@$(DAFNY) build --target go --output $(DFY_OUT) $(DFY_SRCS)

dafny: $(GO_SRC)

# Compile Go source → native binary
# Use GOPATH mode (GO111MODULE=off) since Dafny emits GOPATH-style imports
$(BINARY): $(GO_SRC)
	@mkdir -p $(BUILD_DIR)
	@$(call log,Compiling Go source)
	@GOPATH=$(abspath $(DFY_OUT)-go) GO111MODULE=off \
		$(GO) build -C $(abspath $(GO_SRC)) -o $(abspath $(BINARY)) .

clean:
	@$(call log,Cleaning build directory)
	@rm -rf $(BUILD_DIR)/
