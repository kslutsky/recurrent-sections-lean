# Optional local Linux test environment. The repository is mounted read-only
# at /source and copied into a Docker volume; host build caches are not reused.
FROM ubuntu:24.04
ARG TARGETARCH
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl git python3 python3-venv build-essential \
    libseccomp-dev libgmp-dev pkg-config zstd xz-utils \
    && useradd --create-home --uid 1001 checker \
    && mkdir /workspace && chown checker:checker /workspace
RUN case "$TARGETARCH" in \
      arm64) goarch=arm64 ;; \
      amd64) goarch=amd64 ;; \
      *) exit 1 ;; \
    esac && curl -fsSL "https://go.dev/dl/go1.24.0.linux-${goarch}.tar.gz" \
      | tar -xz -C /usr/local
USER checker
ENV PATH="/home/checker/.elan/bin:/home/checker/.cargo/bin:/usr/local/go/bin:${PATH}"
WORKDIR /home/checker
RUN case "$TARGETARCH" in \
      arm64) triple=aarch64-unknown-linux-gnu ;; \
      amd64) triple=x86_64-unknown-linux-gnu ;; \
      *) exit 1 ;; \
    esac && curl -fsSL \
      "https://github.com/leanprover/elan/releases/download/v4.2.3/elan-${triple}.tar.gz" \
      -o /tmp/elan.tar.gz && tar -xzf /tmp/elan.tar.gz -C /tmp \
      && /tmp/elan-init -y --no-modify-path --default-toolchain none \
      && curl -fsSL \
      "https://static.rust-lang.org/rustup/archive/1.28.2/${triple}/rustup-init" \
      -o /tmp/rustup-init && chmod +x /tmp/rustup-init \
      && /tmp/rustup-init -y --no-modify-path --profile minimal --default-toolchain 1.97.1
WORKDIR /workspace
CMD ["sleep", "infinity"]
