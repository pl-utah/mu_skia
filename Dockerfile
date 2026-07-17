FROM ubuntu:24.04

ARG REPO_URL=https://github.com/pl-utah/mu_skia.git
ARG REPO_REF=main

RUN apt-get update \
    && apt-get install -y --no-install-recommends curl git ca-certificates python3 libegl1 libgl1 \
    && rm -rf /var/lib/apt/lists/* \
    && curl --proto '=https' --tlsv1.2 -sSf https://elan.lean-lang.org/elan-init.sh \
       | sh -s -- -y --default-toolchain none \
    && curl --proto '=https' --tlsv1.2 -LsSf https://astral.sh/uv/install.sh \
       | sh

ENV PATH="/root/.elan/bin:/root/.local/bin:${PATH}"
ENV HOME_DIR=/home/mu_skia
ENV HOME=${HOME_DIR}
ENV ELAN_HOME=/root/.elan
ENV REPO_DIR=${HOME_DIR}/mu_skia

WORKDIR ${HOME_DIR}

# Build the complete evaluation environment so runtime execution needs no
# repository or dependency downloads.
RUN git clone --depth 1 --branch "${REPO_REF}" "${REPO_URL}" "${REPO_DIR}"
WORKDIR ${REPO_DIR}
RUN lake update \
    && lake build \
    && uv sync --locked

WORKDIR ${HOME_DIR}

COPY kick_the_tires.sh ${HOME_DIR}/kick_the_tires.sh
COPY evaluation.sh ${HOME_DIR}/evaluation.sh
RUN chmod +x ${HOME_DIR}/kick_the_tires.sh ${HOME_DIR}/evaluation.sh

CMD ["bash"]
