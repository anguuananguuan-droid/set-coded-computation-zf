# Reproducing the proofs

The supported environment is **Isabelle2025-2** with **AFP 2026-02-06**.
The machine session uses only Isabelle/ZF. The model-theoretic sessions also
need the AFP entry `Independence_CH` and its dependencies.

## Local build

Install [Isabelle2025-2](https://isabelle.in.tum.de/website-Isabelle2025-2/)
for your platform and put its `bin` directory on your path. From this repository:

```sh
isabelle build -v -D Turing_Machines_ZF
```

For the complete development, extract the
[fixed AFP snapshot](https://isa-afp.org/release/afp-2026-02-06.tar.gz) and register it:

```sh
isabelle components -u /absolute/path/to/afp-2026-02-06/thys
isabelle build -v -D .
```

The sessions are ordered as follows:

```text
ZF
└── Turing_Machines_ZF   machines, coding, arithmetic, workspace preservation
    └── Turing_CH       invariance and the conditional EPQ connection
        └── Turing_Models   finite witnesses in transitive ZFC models
```

`Turing_CH` imports AFP theories. `Turing_Models` extends its heap so that
iterations on the witness theory do not recheck the CH development.

The default session timeout is 300 seconds. On a slower machine, use:

```sh
isabelle build -v -j 1 -o threads=2 -o timeout=1800 -D .
```

A successful build exits with status 0. Isabelle may reuse an unchanged session
heap; use `-c` when a clean rebuild of the selected sessions is required.

## Continuous integration

The [GitHub Actions workflow](../.github/workflows/isabelle.yml) runs all three
sessions on Ubuntu 24.04, using GitHub actions pinned to release commits. It caches the downloaded distributions, checks local
Markdown links and scans project theories for proof escapes, then runs the
complete Isabelle build. Build logs are attached to each run. The scan is a
small repository check; the Isabelle kernel is responsible for proof checking.

The dependency installer is [scripts/install-ci.sh](../scripts/install-ci.sh).
It verifies these SHA-256 checksums before extraction:

| Download | SHA-256 |
| :--- | :--- |
| `Isabelle2025-2_linux.tar.gz` | `a20a507bc7c1270d8be96a9f3fbec06345387789d2dc2c4d3df6260d47bfb33c` |
| `afp-2026-02-06.tar.gz` | `b059edd46073479ee8dde45004c2346a7365e5d94cded49d27257cfea66c8879` |

The Isabelle checksum is published in its
[distribution index](https://isabelle.in.tum.de/website-Isabelle2025-2/dist/index.html).
The AFP checksum identifies the archived snapshot used for this development.
The dependencies are downloaded separately and are not redistributed here.

For the documentation and source check alone:

```sh
python3 scripts/check_repository.py
git diff --check
```

Successful proof checking establishes the stated theorems from their explicit
definitions and assumptions. It does not establish that a proposed definition
captures an intended informal claim; the [research review](../papers/REVIEW_AND_ROADMAP.md)
records that distinction and the changes it has required.
