DAFNY   := dafny
GO      := go
NAME    := drb

# Dafny appends "-go" to the --output path, so build/src → build/src-go
BUILD_DIR := build
DFY_OUT   := $(BUILD_DIR)/src
GO_SRC    := $(DFY_OUT)-go/src
BINARY    := $(BUILD_DIR)/$(NAME)

DFY_SRCS := $(wildcard *.dfy)

.PHONY: all verify dafny clean

all: $(BINARY)

# Verify proofs without producing output
verify:
	$(DAFNY) verify $(DFY_SRCS)

# Compile Dafny → Go source
$(GO_SRC): $(DFY_SRCS)
	@$(DAFNY) build --target go --output $(DFY_OUT) $(DFY_SRCS)

dafny: $(GO_SRC)

# Compile Go source → native binary
# Use GOPATH mode (GO111MODULE=off) since Dafny emits GOPATH-style imports
$(BINARY): $(GO_SRC)
	@mkdir -p $(BUILD_DIR)
	@GOPATH=$(abspath $(DFY_OUT)-go) GO111MODULE=off \
		$(GO) build -C $(abspath $(GO_SRC)) -o $(abspath $(BINARY)) .

clean:
	@rm -rf $(BUILD_DIR)/
