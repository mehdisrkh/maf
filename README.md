Summary-Based Compositional Analysis for Soft Contract Verification - Artifact
===============================================================================

This repository contains the software artifact for the paper "Summary-Based Compositional Analysis for Soft Contract Verification".

## Running the Artifact

The artifact can be executed in two ways: by building it from source or by executing our pre-built Docker image.
The commands listed below will create a Docker image in the local Docker installation named `scam-scv-2022-artifact`.

### Building from Source

To build the artifact from source, an included `Dockerfile` can be used. This `Dockerfile` contains all the commands necessary to set-up a suitable building environment.
It can be executed using the following command: 

```
./scripts/artifact/build_from_source.sh 
```

### Running the existing Docker image

In order to run the pre-built Docker image, it first needs to be imported in the Docker environment:

```
./scripts/artifact/import_image.sh
```

Followed by:

```
./scripts/artifact/run_benchmarks.sh $PWD/results/
```

The second argument of the command above can be used to change the location of the CSV files that contain the benchmark results.

## Reproducing Tables

To reproduce the tables included in the paper, the benchmark programs can be executed, and their results analyzed. 
For convience a script is included that generates the tables for the paper, and outputs them in LaTeX format:

```
./scripts/artifact/run_and_build_tables.sh $PWD/results/
```

The command above will run the benchmarks and their Python processing scripts. All processing scripts can be found in the `scripts/Python/scv/` directory.

## Code Navigation

* Section 3A: syntax of the contract language is provided by the following files and packages:
   - `code/shared/src/main/scala/maf/language/scheme/SchemeExp.scala`: defines the AST elements as subklasses of `ContractSchemeExp`
   - `code/shared/src/main/scala/maf/language/ContractScheme/`: provides various preprocessing code for parsing the code ofprograms written in the contract language.
* Section 3B: concrete semantics, in big-step form can be found in the following files and packages:
   - `code/shared/src/main/scala/maf/language/ContractScheme/ContractValues.scala` contains definitions for all contract related values used by the interpreter 
   - `code/shared/src/main/scala/maf/language/ContractScheme/interpreter/` provides a concrete interpreter for soundness testing.
* Section 4: 
   - `code/shared/src/main/scala/maf/language/scheme/lattices/ModularSchemeLattice.scala` provides the abstract domain for the static analysis.
   - `code/shared/src/main/scala/maf/modular/scv/ScvBigStepSemantics.scala` describes the abstract semantics of the contract language in a big step style. It descends from a ModF analysis from the MAF framework, which implies the usage of a global store, and provides the notion of "components" and effects between them. 
   - `code/shared/src/main/scala/maf/modular/scv/FunctionSummary.scala` provides the implementation of function summaries as well as the two phase-analysis of collection and propagation.
* Section 6B: 
   - `maf.cli.experiments.aam.ScvPerformanceComparison` implements the performance (in terms of execution time) benchmarks described in the paper. 
   - `maf.cli.experiments.scv.CountFalsePositives` implements the precision (in terms of false positives) benchmarks described in the papers.


## Badges

Our artifact satisfies the following criteria:

* Available: this artifact is archived at TODO ADD DOI here. The artifact is provided under an open source license (GPLv3), with a commercial use exception (see LICENSE.md).
* Functional: this artifact provides scripts to regenerate the results presented in the paper (see above)
* Reusable: the artifact can be extended and reused for other purposes.  We provide documentation is this README with pointers to the relevant files, as well as source code documentation in the source itself. 
