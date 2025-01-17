################################################################################
## project base
## https://stackoverflow.com/questions/18136918/how-to-get-current-relative-directory-of-your-makefile
################################################################################
MAKEFILE_PATH := $(abspath $(lastword $(MAKEFILE_LIST)))
PROJECT_DIRPATH := $(dir $(MAKEFILE_PATH))

################################################################################
## Parallelism
################################################################################
CPU_COUNT := 70

################################################################################
## Github
################################################################################
AVIRALG_GIT_URL := git@github.com:aviralg
PRL_PRG_GIT_URL := git@github.com:PRL-PRG

# logs
LOGS_DIRPATH := $(PROJECT_DIRPATH)/logs

# dependency
DEPENDENCY_DIRPATH := $(PROJECT_DIRPATH)/dependency
LOGS_DEPENDENCY_DIRPATH := $(LOGS_DIRPATH)/dependency

## dependency/dirpath
DOCKR_BRANCH := master
DOCKR_GIT_URL := $(AVIRALG_GIT_URL)/dockr.git
DEPENDENCY_DOCKR_DIRPATH := $(DEPENDENCY_DIRPATH)/dockr
LOGS_DEPENDENCY_DOCKR_DIRPATH := $(LOGS_DEPENDENCY_DIRPATH)/dockr/

## dependency/r-vanilla
R_VANILLA_BRANCH := r-4.0.2
R_VANILLA_GIT_URL := $(PRL_PRG_GIT_URL)/R-vanilla.git
DEPENDENCY_R_VANILLA_DIRPATH := $(DEPENDENCY_DIRPATH)/R-vanilla
LOGS_DEPENDENCY_R_VANILLA_DIRPATH := $(LOGS_DEPENDENCY_DIRPATH)/R-vanilla
R_VANILLA_BIN := $(DEPENDENCY_R_VANILLA_DIRPATH)/bin/R

## dependency/r-dyntrace
R_DYNTRACE_BRANCH := r-4.0.2
R_DYNTRACE_GIT_URL := $(PRL_PRG_GIT_URL)/R-dyntrace.git
DEPENDENCY_R_DYNTRACE_DIRPATH := $(DEPENDENCY_DIRPATH)/R-dyntrace
LOGS_DEPENDENCY_R_DYNTRACE_DIRPATH := $(LOGS_DEPENDENCY_DIRPATH)/R-dyntrace
R_DYNTRACE_BIN := $(DEPENDENCY_R_DYNTRACE_DIRPATH)/bin/R

## dependency/library
DEPENDENCY_LIBRARY_DIRPATH := $(DEPENDENCY_DIRPATH)/library
LOGS_DEPENDENCY_LIBRARY_DIRPATH := $(LOGS_DEPENDENCY_DIRPATH)/library

### dependency/library/mirror
DEPENDENCY_LIBRARY_MIRROR_DIRPATH := $(DEPENDENCY_LIBRARY_DIRPATH)/mirror
LOGS_DEPENDENCY_LIBRARY_MIRROR_DIRPATH := $(LOGS_DEPENDENCY_LIBRARY_DIRPATH)/mirror

#### dependency/library/mirror/cran
DEPENDENCY_LIBRARY_MIRROR_CRAN_DIRPATH := $(DEPENDENCY_LIBRARY_MIRROR_DIRPATH)/cran
LOGS_DEPENDENCY_LIBRARY_MIRROR_CRAN_DIRPATH := $(LOGS_DEPENDENCY_LIBRARY_MIRROR_DIRPATH)/cran

### dependency/library/extract
DEPENDENCY_LIBRARY_EXTRACT_DIRPATH := $(DEPENDENCY_LIBRARY_DIRPATH)/extract
LOGS_DEPENDENCY_LIBRARY_EXTRACT_DIRPATH := $(LOGS_DEPENDENCY_LIBRARY_DIRPATH)/extract

### dependency/library/install
DEPENDENCY_LIBRARY_INSTALL_DIRPATH := $(DEPENDENCY_LIBRARY_DIRPATH)/install
LOGS_DEPENDENCY_LIBRARY_INSTALL_DIRPATH := $(LOGS_DEPENDENCY_LIBRARY_DIRPATH)/install

#### dependency/library/install/cran
LOGS_DEPENDENCY_LIBRARY_INSTALL_CRAN_DIRPATH := $(LOGS_DEPENDENCY_LIBRARY_INSTALL_DIRPATH)/cran

## dependency/instrumentr
INSTRUMENTR_BRANCH := c-api-envtracer
INSTRUMENTR_GIT_URL := $(PRL_PRG_GIT_URL)/instrumentr.git
DEPENDENCY_INSTRUMENTR_DIRPATH := $(DEPENDENCY_DIRPATH)/instrumentr
LOGS_DEPENDENCY_INSTRUMENTR_DIRPATH := $(LOGS_DEPENDENCY_DIRPATH)/instrumentr

## dependency/experimentr
EXPERIMENTR_BRANCH := master
EXPERIMENTR_GIT_URL := $(AVIRALG_GIT_URL)/experimentr.git
DEPENDENCY_EXPERIMENTR_DIRPATH := $(DEPENDENCY_DIRPATH)/experimentr
LOGS_DEPENDENCY_EXPERIMENTR_DIRPATH := $(LOGS_DEPENDENCY_DIRPATH)/experimentr

## dependency/envtracer
ENVTRACER_BRANCH := master
ENVTRACER_GIT_URL := $(AVIRALG_GIT_URL)/envtracer.git
DEPENDENCY_ENVTRACER_DIRPATH := $(DEPENDENCY_DIRPATH)/envtracer
LOGS_DEPENDENCY_ENVTRACER_DIRPATH := $(LOGS_DEPENDENCY_DIRPATH)/envtracer

# analysis
ANALYSIS_DIRPATH := $(PROJECT_DIRPATH)/analysis

# experiment
EXPERIMENT_DIRPATH := $(PROJECT_DIRPATH)/experiment

## experiment/corpus
EXPERIMENT_CORPUS_DIRPATH := $(EXPERIMENT_DIRPATH)/corpus
LOGS_CORPUS_DIRPATH := $(LOGS_DIRPATH)/corpus

### experiment/corpus/extract
EXPERIMENT_CORPUS_EXTRACT_DIRPATH := $(EXPERIMENT_CORPUS_DIRPATH)/extract
EXPERIMENT_CORPUS_EXTRACT_INDEX_FILEPATH := $(EXPERIMENT_CORPUS_EXTRACT_DIRPATH)/index.fst
EXPERIMENT_CORPUS_EXTRACT_PROGRAMS_DIRPATH := $(EXPERIMENT_CORPUS_EXTRACT_DIRPATH)/programs
LOGS_CORPUS_EXTRACT_DIRPATH := $(LOGS_CORPUS_DIRPATH)/extract

### experiment/corpus/sloc
EXPERIMENT_CORPUS_SLOC_DIRPATH := $(EXPERIMENT_CORPUS_DIRPATH)/sloc
LOGS_CORPUS_SLOC_DIRPATH := $(LOGS_CORPUS_DIRPATH)/sloc

#### experiment/corpus/sloc/corpus
EXPERIMENT_CORPUS_SLOC_CORPUS_DIRPATH := $(EXPERIMENT_CORPUS_SLOC_DIRPATH)/corpus
EXPERIMENT_CORPUS_SLOC_CORPUS_FILEPATH := $(EXPERIMENT_CORPUS_SLOC_CORPUS_DIRPATH)/sloc.fst
LOGS_CORPUS_SLOC_CORPUS_DIRPATH := $(LOGS_CORPUS_SLOC_DIRPATH)/corpus

#### experiment/corpus/sloc/corpus
EXPERIMENT_CORPUS_SLOC_PACKAGE_DIRPATH := $(EXPERIMENT_CORPUS_SLOC_DIRPATH)/package
EXPERIMENT_CORPUS_SLOC_PACKAGE_FILEPATH := $(EXPERIMENT_CORPUS_SLOC_PACKAGE_DIRPATH)/sloc.fst
LOGS_CORPUS_SLOC_PACKAGE_DIRPATH := $(LOGS_CORPUS_SLOC_DIRPATH)/package

### experiment/corpus/package
EXPERIMENT_CORPUS_PACKAGE_DIRPATH := $(EXPERIMENT_CORPUS_DIRPATH)/package
EXPERIMENT_CORPUS_PACKAGE_INFO_FILEPATH := $(EXPERIMENT_CORPUS_PACKAGE_DIRPATH)/info.fst
LOGS_CORPUS_PACKAGE_DIRPATH := $(LOGS_CORPUS_DIRPATH)/package

## experiment/profile
EXPERIMENT_PROFILE_DIRPATH := $(EXPERIMENT_DIRPATH)/profile
LOGS_PROFILE_DIRPATH := $(LOGS_DIRPATH)/profile

### experiment/profile/trace
EXPERIMENT_PROFILE_TRACE_DIRPATH := $(EXPERIMENT_PROFILE_DIRPATH)/trace

EXPERIMENT_PROFILE_TRACE_PROGRAMS_DIRPATH := $(EXPERIMENT_PROFILE_TRACE_DIRPATH)/programs
EXPERIMENT_PROFILE_TRACE_PROGRAMS_JOBLOG_FILEPATH := $(EXPERIMENT_PROFILE_TRACE_PROGRAMS_DIRPATH)/trace-joblog

EXPERIMENT_PROFILE_TRACE_INDEX_DIRPATH := $(EXPERIMENT_PROFILE_TRACE_DIRPATH)/index
EXPERIMENT_PROFILE_TRACE_INDEX_PROGRAMS_FILEPATH = $(EXPERIMENT_PROFILE_TRACE_INDEX_DIRPATH)/programs
EXPERIMENT_PROFILE_TRACE_INDEX_OUTDIR_FILEPATH = $(EXPERIMENT_PROFILE_TRACE_INDEX_DIRPATH)/outdir
EXPERIMENT_PROFILE_TRACE_INDEX_LOGDIR_FILEPATH = $(EXPERIMENT_PROFILE_TRACE_INDEX_DIRPATH)/logdir
EXPERIMENT_PROFILE_TRACE_INDEX_CORPUS_FILEPATH = $(EXPERIMENT_PROFILE_TRACE_INDEX_DIRPATH)/corpus
EXPERIMENT_PROFILE_TRACE_INDEX_CLIENT_FILEPATH = $(EXPERIMENT_PROFILE_TRACE_INDEX_DIRPATH)/client

LOGS_PROFILE_TRACE_DIRPATH := $(LOGS_PROFILE_DIRPATH)/trace

### experiment/profile/reduce
ANALYSIS := signature
ANALYSIS_PROFILE_SCRIPT := $(ANALYSIS_DIRPATH)/analysis.R
EXPERIMENT_PROFILE_REDUCE_PROGRAMS_JOBLOG_FILEPATH := $(EXPERIMENT_PROFILE_TRACE_PROGRAMS_DIRPATH)/reduce-joblog

### experiment/profile/combine
EXPERIMENT_PROFILE_COMBINE_DIRPATH := $(EXPERIMENT_PROFILE_DIRPATH)/combine

### experiment/profile/summarize
EXPERIMENT_PROFILE_SUMMARIZE_DIRPATH := $(EXPERIMENT_PROFILE_DIRPATH)/summarize

### experiment/profile/signature
ANALYSIS_SIGNATURE_SCRIPT := $(ANALYSIS_DIRPATH)/signature.R
EXPERIMENT_PROFILE_SIGNATURE_DIRPATH := $(EXPERIMENT_PROFILE_DIRPATH)/signature

## experiment/validate
SIGNATURE := signature+force+effect+reflection
EXPERIMENT_VALIDATE_DIRPATH := $(EXPERIMENT_DIRPATH)/validate
LOGS_VALIDATE_DIRPATH := $(LOGS_DIRPATH)/validate

### experiment/validate/trace
EXPERIMENT_VALIDATE_TRACE_DIRPATH := $(EXPERIMENT_VALIDATE_DIRPATH)/trace

EXPERIMENT_VALIDATE_TRACE_PROGRAMS_DIRPATH := $(EXPERIMENT_VALIDATE_TRACE_DIRPATH)/programs
EXPERIMENT_VALIDATE_TRACE_PROGRAMS_JOBLOG_DIRPATH := $(EXPERIMENT_VALIDATE_TRACE_PROGRAMS_DIRPATH)/joblog

EXPERIMENT_VALIDATE_TRACE_INDEX_DIRPATH := $(EXPERIMENT_VALIDATE_TRACE_DIRPATH)/index
EXPERIMENT_VALIDATE_TRACE_INDEX_PROGRAMS_FILEPATH = $(EXPERIMENT_VALIDATE_TRACE_INDEX_DIRPATH)/programs
EXPERIMENT_VALIDATE_TRACE_INDEX_OUTDIR_FILEPATH = $(EXPERIMENT_VALIDATE_TRACE_INDEX_DIRPATH)/outdir
EXPERIMENT_VALIDATE_TRACE_INDEX_LOGDIR_FILEPATH = $(EXPERIMENT_VALIDATE_TRACE_INDEX_DIRPATH)/logdir
EXPERIMENT_VALIDATE_TRACE_INDEX_CORPUS_FILEPATH = $(EXPERIMENT_VALIDATE_TRACE_INDEX_DIRPATH)/corpus
EXPERIMENT_VALIDATE_TRACE_INDEX_CLIENT_FILEPATH = $(EXPERIMENT_VALIDATE_TRACE_INDEX_DIRPATH)/client

LOGS_VALIDATE_TRACE_DIRPATH := $(LOGS_VALIDATE_DIRPATH)/trace
ANALYSIS_VALIDATE_SCRIPT := $(ANALYSIS_DIRPATH)/validate.R

TYPE := example
PACKAGE := ACNE
FILENAME := fitSnpNmfArray

## experiment/validate/summary
EXPERIMENT_VALIDATE_SUMMARY_DIRPATH := $(EXPERIMENT_VALIDATE_DIRPATH)/summary

## experiment/report
EXPERIMENT_REPORT_DIRPATH := $(EXPERIMENT_DIRPATH)/report
LOGS_REPORT_DIRPATH := $(LOGS_DIRPATH)/report

## experiment/report/paper
PAPER_BRANCH := master
PAPER_GIT_URL := $(AVIRALG_GIT_URL)/envtracing-paper.git
EXPERIMENT_REPORT_PAPER_DIRPATH := $(EXPERIMENT_REPORT_DIRPATH)/paper
LOGS_REPORT_PAPER_DIRPATH := $(LOGS_REPORT_DIRPATH)/paper

## experiment/report/input
EXPERIMENT_REPORT_PAPER_DATA_DIRPATH := $(EXPERIMENT_REPORT_PAPER_DIRPATH)/data
LOGS_REPORT_INPUT_DIRPATH := $(LOGS_REPORT_DIRPATH)/input

## experiment/report/update
LOGS_REPORT_UPDATE_DIRPATH := $(LOGS_REPORT_DIRPATH)/update

## experiment/report/render
LOGS_REPORT_RENDER_DIRPATH := $(LOGS_REPORT_DIRPATH)/render

PACKAGE_LIST := installed.packages()[,1]

################################################################################
## parallel args
################################################################################
TIMEOUT := 7200
PARALLEL_ARGS := --bar --eta --timeout $(TIMEOUT) --wd ... --jobs=$(CPU_COUNT) --files

################################################################################
## docker build args
################################################################################
#PORT := 5000:80
USER := $(USER)
UID := $(shell id -u)
GID := $(shell id -g)
PASSWORD := $(USER)
R_LIBS_USER := $(DEPENDENCY_LIBRARY_INSTALL_DIRPATH)

R_DYNTRACE := $(PROJECT_DIRPATH)R-dyntrace/bin/R
DOCKR_RUN_ARGS := -t --env="DISPLAY" --volume="/tmp/.X11-unix:/tmp/.X11-unix" --cap-add=SYS_PTRACE --security-opt seccomp=unconfined --privileged -v $(PROJECT_DIRPATH):$(PROJECT_DIRPATH) #--publish=$(PORT)

################################################################################
## Applications
################################################################################
TEE := tee
TEE_FLAGS := -i
TIME := time --portability
XVFB_RUN := xvfb-run
MV := mv
RM := rm
PARALLEL := parallel

DATE := TZ='America/New_York' date +"%Y-%b-%d %I:%M:%S %p"
################################################################################
## package setup options
################################################################################
CRAN_MIRROR_URL := "https://cran.r-project.org"
PACKAGE_SETUP_REPOSITORIES := --setup-cran --setup-bioc
PACKAGE_SETUP_NCPUS := 8
PACKAGE_SETUP_DIRPATH := $(PROJECT_DIRPATH)packages
PACKAGE_LIB_DIRPATH := $(PACKAGE_SETUP_DIRPATH)/lib
PACKAGE_MIRROR_DIRPATH := $(PACKAGE_SETUP_DIRPATH)/mirror
PACKAGE_SRC_DIRPATH := $(PACKAGE_SETUP_DIRPATH)/src
PACKAGE_TEST_DIRPATH := $(PACKAGE_SETUP_DIRPATH)/tests
PACKAGE_EXAMPLE_DIRPATH := $(PACKAGE_SETUP_DIRPATH)/examples
PACKAGE_VIGNETTE_DIRPATH := $(PACKAGE_SETUP_DIRPATH)/doc
PACKAGE_LOG_DIRPATH := $(PACKAGE_SETUP_DIRPATH)/log

################################################################################
## corpus
################################################################################
CORPUS_DIRPATH := $(PROJECT_DIRPATH)corpus
CORPUS_INDEX_DIRPATH := $(CORPUS_DIRPATH)/index
CORPUS_DATA_DIRPATH := $(CORPUS_DIRPATH)/data
CORPUS_LOGS_DIRPATH := $(CORPUS_DIRPATH)/logs
CORPUS_INDEX_ALL_FILEPATH := $(CORPUS_INDEX_DIRPATH)/all.fst
CORPUS_DATA_ALL_DIRPATH := $(CORPUS_DATA_DIRPATH)/all

initialize:
	mkdir library

docker-image:
	docker build                            \
	       --build-arg USER=$(USER)         \
	       --build-arg UID=$(UID)           \
	       --build-arg GID=$(GID)           \
	       --build-arg PASSWORD=$(PASSWORD) \
	       --tag dockr                      \
	       .

docker-container:
	docker run                                        \
	       -d                                         \
	       --interactive                              \
	       --tty                                      \
	       $(DOCKR_RUN_ARGS)                          \
	       dockr                                      \
	       fish

docker-shell:
	docker run                                        \
	       --interactive                              \
	       --tty                                      \
	       $(DOCKR_RUN_ARGS)                          \
	       dockr                                      \
	       fish

docker-r-dyntrace:
	docker run                                        \
	       --interactive                              \
	       --tty                                      \
	       $(DOCKR_RUN_ARGS)                          \
	       dockr                                      \
	       $(R_DYNTRACE_BIN)

define newline


endef

# https://gist.github.com/nicferrier/2277987
define clonepull
if [ ! -d ${3}/.git ]; then                                            \
    git clone --branch ${1} ${2} ${3} 2>&1 | $(TEE) $(TEE_FLAGS) ${4}; \
else                                                                   \
    cd ${3} && git pull origin ${1} 2>&1 | $(TEE) $(TEE_FLAGS) ${4};   \
fi;
endef

define dockr_parallel
docker run $(DOCKR_RUN_ARGS) dockr $(PARALLEL) ${1}
endef


define dockr_rdyntrace
docker run $(DOCKR_RUN_ARGS) dockr $(R_DYNTRACE_BIN) -e ${1} 2>&1 | $(TEE) $(TEE_FLAGS) ${2}
endef

define dockr_rdyntrace_file
docker run $(DOCKR_RUN_ARGS) dockr $(R_DYNTRACE_BIN) -f ${1} 2>&1 | $(TEE) $(TEE_FLAGS) ${2}
endef

define dockr_rvanilla
docker run $(DOCKR_RUN_ARGS) dockr $(R_VANILLA_BIN) -e ${1} 2>&1 | $(TEE) $(TEE_FLAGS) ${2}
endef

define dockr_rvanilla_file
docker run $(DOCKR_RUN_ARGS) dockr $(R_VANILLA_BIN) -f ${1} 2>&1 | $(TEE) $(TEE_FLAGS) ${2}
endef

define dockr_bash
docker run $(DOCKR_RUN_ARGS) dockr bash -c ${1} 2>&1 | $(TEE) $(TEE_FLAGS) ${2}
endef

define tee
${1} 2>&1 | $(TEE) $(TEE_FLAGS) ${2}
endef

define dockr_make
$(call tee, docker run $(DOCKR_RUN_ARGS) dockr make ${1}, ${2})
endef

define r_code
"$(subst $(newline), ,${1})"
endef

define CUSTOM_INSTALL_CODE
install.packages($(PACKAGE_LIST),repos = \"http://cran.us.r-project.org\")
endef


install-custom-packages:
	echo "begin"
	$(call dockr_rdyntrace, "$(subst $(newline), ,$(CUSTOM_INSTALL_CODE))", "/tmp/custom.log")
	echo "here"

.PHONY: install-custom-packages

################################################################################
## dependency
################################################################################

dependency: dependency-dockr       \
            dependency-r-vanilla   \
            dependency-r-dyntrace  \
            dependency-library     \
            dependency-instrumentr \
            dependency-experimentr \
            dependency-envtracer

################################################################################
## dependency/dockr
################################################################################

dependency-dockr:
	mkdir -p $(DEPENDENCY_DIRPATH)
	mkdir -p $(LOGS_DEPENDENCY_DIRPATH)
	mkdir -p $(LOGS_DEPENDENCY_DOCKR_DIRPATH)
	$(call clonepull, $(DOCKR_BRANCH), $(DOCKR_GIT_URL), $(DEPENDENCY_DOCKR_DIRPATH), $(LOGS_DEPENDENCY_DOCKR_DIRPATH)/clone.log)
	docker build                                   \
	       --build-arg USER=$(USER)                \
	       --build-arg UID=$(UID)                  \
	       --build-arg GID=$(GID)                  \
	       --build-arg PASSWORD=$(PASSWORD)        \
	       --build-arg R_LIBS_USER=$(R_LIBS_USER)  \
	       --tag dockr                             \
	       $(DEPENDENCY_DOCKR_DIRPATH) 2>&1 | $(TEE) $(TEE_FLAGS) $(LOGS_DEPENDENCY_DOCKR_DIRPATH)/build.log

################################################################################
## dependency/r-vanilla
################################################################################

dependency-r-vanilla:
	mkdir -p $(DEPENDENCY_DIRPATH)
	mkdir -p $(LOGS_DEPENDENCY_R_VANILLA_DIRPATH)
	$(call clonepull, $(R_VANILLA_BRANCH), $(R_VANILLA_GIT_URL), $(DEPENDENCY_R_VANILLA_DIRPATH), $(LOGS_DEPENDENCY_R_VANILLA_DIRPATH)/clone.log)
	$(call dockr_bash, 'cd $(DEPENDENCY_R_VANILLA_DIRPATH) && ./build', $(LOGS_DEPENDENCY_R_VANILLA_DIRPATH)/build.log)

################################################################################
## dependency/r-dyntrace
################################################################################

dependency-r-dyntrace:
	mkdir -p $(DEPENDENCY_DIRPATH)
	mkdir -p $(LOGS_DEPENDENCY_R_DYNTRACE_DIRPATH)
	$(call clonepull, $(R_DYNTRACE_BRANCH), $(R_DYNTRACE_GIT_URL), $(DEPENDENCY_R_DYNTRACE_DIRPATH), $(LOGS_DEPENDENCY_R_DYNTRACE_DIRPATH)/clone.log)
	$(call dockr_bash, 'cd $(DEPENDENCY_R_DYNTRACE_DIRPATH) && ./build', $(LOGS_DEPENDENCY_R_DYNTRACE_DIRPATH)/build.log)

################################################################################
## dependency/library
################################################################################

dependency-library: dependency-library-mirror  \
                    dependency-library-extract \
                    dependency-library-install \
                    dependency-library-snapshot

################################################################################
## dependency/library/mirror
################################################################################

dependency-library-mirror: dependency-library-mirror-cran

################################################################################
## dependency/library/mirror/cran
################################################################################

dependency-library-mirror-cran:
	@mkdir -p $(DEPENDENCY_LIBRARY_MIRROR_CRAN_DIRPATH)
	@mkdir -p $(LOGS_DEPENDENCY_LIBRARY_MIRROR_CRAN_DIRPATH)
	rsync -zrtlv --delete																																	\
	             --include '/src'																													\
	             --include '/src/contrib'																									\
	             --include '/src/contrib/*.tar.gz'																				\
	             --include '/src/contrib/PACKAGES'																				\
	             --include '/src/contrib/Symlink'																					\
	             --include '/src/contrib/Symlink/**'																			\
	             --exclude '**'																														\
	             cran.r-project.org::CRAN $(DEPENDENCY_LIBRARY_MIRROR_CRAN_DIRPATH) \
	             2>&1 | $(TEE) $(TEE_FLAGS) $(LOGS_DEPENDENCY_LIBRARY_MIRROR_CRAN_DIRPATH)/rsync.log

################################################################################
## dependency/library/extract
################################################################################

dependency-library-extract:
	@mkdir -p $(DEPENDENCY_LIBRARY_EXTRACT_DIRPATH)
	@mkdir -p $(LOGS_DEPENDENCY_LIBRARY_EXTRACT_DIRPATH)
	find $(DEPENDENCY_LIBRARY_MIRROR_CRAN_DIRPATH)/src/contrib               \
	     $(DEPENDENCY_LIBRARY_MIRROR_BIOC_RELEASE_DIRPATH)/bioc/src/contrib  \
	     -maxdepth 1                                                               \
	     -type f                                                                   \
	     -name "*.tar.gz"                                                          \
	     -execdir tar -xvf '{}'                                                    \
	     -C $(DEPENDENCY_LIBRARY_EXTRACT_DIRPATH) \; 2>&1 | $(TEE) $(TEE_FLAGS) $(LOGS_DEPENDENCY_LIBRARY_EXTRACT_DIRPATH)/tar.log

################################################################################
## dependency/library/install
################################################################################

dependency-library-install: dependency-library-install-cran

define INSTALL_CRAN_PACKAGES_CODE
options(repos       = 'file://$(DEPENDENCY_LIBRARY_MIRROR_CRAN_DIRPATH)');
options(BioC_mirror = 'file://$(DEPENDENCY_LIBRARY_MIRROR_BIOC_DIRPATH)');
packages <- setdiff(available.packages()[,1], installed.packages()[,1]);
cat('Installing', length(packages), 'packages with', $(CPU_COUNT), 'cpus\n');
install.packages(packages,
                 Ncpus = $(CPU_COUNT),
                 keep_outputs = TRUE,
                 INSTALL_opts = c('--example',
                                  '--install-tests',
                                  '--with-keep.source',
                                  '--no-multiarch'),
                 dependencies = c('Depends',
                                  'Imports',
                                  'LinkingTo',
                                  'Suggests',
                                  'Enhances'));
endef


################################################################################
## dependency/library/install/cran
################################################################################

dependency-library-install-cran:
	@mkdir -p $(DEPENDENCY_LIBRARY_INSTALL_DIRPATH)
	@mkdir -p $(LOGS_DEPENDENCY_LIBRARY_INSTALL_DIRPATH)
	@mkdir -p $(LOGS_DEPENDENCY_LIBRARY_INSTALL_CRAN_DIRPATH)
	$(call dockr_rdyntrace, "$(subst $(newline), ,$(INSTALL_CRAN_PACKAGES_CODE))", $(LOGS_DEPENDENCY_LIBRARY_INSTALL_CRAN_DIRPATH)/install.log)
	$(MV) -f *.out $(LOGS_DEPENDENCY_LIBRARY_INSTALL_CRAN_DIRPATH) 2> /dev/null

################################################################################
## dependency/instrumentr
################################################################################

dependency-instrumentr:
	@mkdir -p $(DEPENDENCY_DIRPATH)
	@mkdir -p $(LOGS_DEPENDENCY_INSTRUMENTR_DIRPATH)
	$(call clonepull, $(INSTRUMENTR_BRANCH), $(INSTRUMENTR_GIT_URL), $(DEPENDENCY_INSTRUMENTR_DIRPATH), $(LOGS_DEPENDENCY_INSTRUMENTR_DIRPATH)/clone.log)
	$(call dockr_make, -C $(DEPENDENCY_INSTRUMENTR_DIRPATH) R=$(R_DYNTRACE_BIN), $(LOGS_DEPENDENCY_INSTRUMENTR_DIRPATH)/install.log)

################################################################################
## dependency/experimentr
################################################################################

dependency-experimentr:
	@mkdir -p $(DEPENDENCY_DIRPATH)
	@mkdir -p $(LOGS_DEPENDENCY_EXPERIMENTR_DIRPATH)
	$(call clonepull, $(EXPERIMENTR_BRANCH), $(EXPERIMENTR_GIT_URL), $(DEPENDENCY_EXPERIMENTR_DIRPATH), $(LOGS_DEPENDENCY_EXPERIMENTR_DIRPATH)/clone.log)
	$(call dockr_make, -C $(DEPENDENCY_EXPERIMENTR_DIRPATH) R=$(R_DYNTRACE_BIN), $(LOGS_DEPENDENCY_EXPERIMENTR_DIRPATH)/install.log)

################################################################################
## dependency/envtracer
################################################################################

dependency-envtracer:
	@mkdir -p $(DEPENDENCY_DIRPATH)
	@mkdir -p $(LOGS_DEPENDENCY_ENVTRACER_DIRPATH)
	$(call clonepull,$(ENVTRACER_BRANCH), $(ENVTRACER_GIT_URL), $(DEPENDENCY_ENVTRACER_DIRPATH), $(LOGS_DEPENDENCY_ENVTRACER_DIRPATH)/clone.log)
	$(call dockr_make, -C $(DEPENDENCY_ENVTRACER_DIRPATH) R=$(R_DYNTRACE_BIN), $(LOGS_DEPENDENCY_ENVTRACER_DIRPATH)/install.log)

################################################################################
## experiment
################################################################################

experiment: experiment-corpus		\
            experiment-profile	\
            experiment-remove		\
            experiment-analyze

################################################################################
## experiment/corpus
################################################################################

experiment-corpus: experiment-corpus-extract       \
                   experiment-corpus-sloc          \
                   experiment-corpus-package       \
                   experiment-corpus-deterministic

define CODE_EXTRACT_CODE
library(experimentr);
res <- extract_code($(PACKAGE_LIST),
                    type=c('example', 'vignette', 'testthat', 'test'),
                    index_filepath='$(EXPERIMENT_CORPUS_EXTRACT_INDEX_FILEPATH)',
                    data_dirpath='$(EXPERIMENT_CORPUS_EXTRACT_PROGRAMS_DIRPATH)');
endef


################################################################################
## experiment/corpus/extract
################################################################################

experiment-corpus-extract:
	mkdir -p $(EXPERIMENT_CORPUS_EXTRACT_DIRPATH)
	$(RM) -rf $(EXPERIMENT_CORPUS_EXTRACT_PROGRAMS_DIRPATH) && mkdir -p $(EXPERIMENT_CORPUS_EXTRACT_PROGRAMS_DIRPATH)
	mkdir -p $(LOGS_CORPUS_EXTRACT_DIRPATH)
	$(call dockr_rdyntrace, "$(subst $(newline), ,$(CODE_EXTRACT_CODE))", $(LOGS_CORPUS_EXTRACT_DIRPATH)/extract.log)

################################################################################
## experiment/corpus/sloc
################################################################################

experiment-corpus-sloc: experiment-corpus-sloc-corpus  \
                        experiment-corpus-sloc-package

################################################################################
## experiment/corpus/sloc/corpus
################################################################################

define CORPUS_SLOC
library(experimentr);
res <- compute_sloc('$(EXPERIMENT_CORPUS_EXTRACT_PROGRAMS_DIRPATH)',
                    output_filepath='$(EXPERIMENT_CORPUS_SLOC_CORPUS_FILEPATH)',
                    echo = TRUE);
endef

experiment-corpus-sloc-corpus:
	mkdir -p $(EXPERIMENT_CORPUS_SLOC_CORPUS_DIRPATH)
	mkdir -p $(LOGS_CORPUS_SLOC_CORPUS_DIRPATH)
	$(call dockr_rdyntrace, "$(subst $(newline), ,$(CORPUS_SLOC))", $(LOGS_CORPUS_SLOC_CORPUS_DIRPATH)/sloc.log)


################################################################################
## experiment/corpus/sloc/package
################################################################################

define PACKAGE_SLOC
library(experimentr);
res <- compute_sloc('$(DEPENDENCY_LIBRARY_EXTRACT_DIRPATH)',
                    output_filepath='$(EXPERIMENT_CORPUS_SLOC_PACKAGE_FILEPATH)',
                    echo = FALSE);
endef

experiment-corpus-sloc-package:
	mkdir -p $(EXPERIMENT_CORPUS_SLOC_PACKAGE_DIRPATH)
	mkdir -p $(LOGS_CORPUS_SLOC_PACKAGE_DIRPATH)
	$(call dockr_rdyntrace, "$(subst $(newline), ,$(PACKAGE_SLOC))", $(LOGS_CORPUS_SLOC_PACKAGE_DIRPATH)/sloc.log)


################################################################################
## experiment/corpus/package
################################################################################

define CORPUS_PACKAGE
library(experimentr);
library(fs);
engine <- gnu_parallel('--progress',
                       '--wd', '$(EXPERIMENT_CORPUS_PACKAGE_DIRPATH)',
                       '--results', '$(LOGS_CORPUS_PACKAGE_DIRPATH)/package_{1}/',
                       '--joblog', '$(LOGS_CORPUS_PACKAGE_DIRPATH)/joblog');
parallelize(
    r_expr('experimentr::get_package_info(\'{}\', output_filepath = \'$(EXPERIMENT_CORPUS_PACKAGE_DIRPATH)/{}.fst\')',
            invisible=TRUE),
    vector_input($(PACKAGE_LIST)),
    engine = engine,
    error_on_status = FALSE
);
files <- dir_ls('$(EXPERIMENT_CORPUS_PACKAGE_DIRPATH)', glob = '*.fst');
invisible(merge_tables(files,
             '$(EXPERIMENT_CORPUS_PACKAGE_INFO_FILEPATH)',
             remove_files=TRUE,
             remove_empty_dirs=TRUE));
log_dirs <- dir_ls('$(LOGS_CORPUS_PACKAGE_DIRPATH)', type = 'directory', recurse = FALSE);
invisible(merge_logs(log_dirs,
           '$(LOGS_CORPUS_PACKAGE_DIRPATH)/joblog',
           '$(EXPERIMENT_CORPUS_PACKAGE_DIRPATH)/job.fst',
           remove_logs = FALSE,
           remove_job_log = FALSE,
           reader = readr::read_file,
           writer = fst::write_fst));
endef

experiment-corpus-package:
	$(RM) -rf $(EXPERIMENT_CORPUS_PACKAGE_DIRPATH)
	mkdir -p $(EXPERIMENT_CORPUS_PACKAGE_DIRPATH)
	$(RM) -rf $(LOGS_CORPUS_PACKAGE_DIRPATH)
	mkdir -p $(LOGS_CORPUS_PACKAGE_DIRPATH)
	$(call dockr_rdyntrace, "$(subst $(newline), ,$(CORPUS_PACKAGE))", $(LOGS_CORPUS_PACKAGE_DIRPATH)/package.log)

experiment-corpus-package-merge:
	$(call dockr_rdyntrace, "$(subst $(newline), ,$(CORPUS_PACKAGE_MERGE))", $(LOGS_CORPUS_PACKAGE_DIRPATH)/package.log)

################################################################################
## experiment/corpus/deterministic
################################################################################
experiment-corpus-deterministic:
	@echo TODO

################################################################################
## experiment/profile
################################################################################
experiment-profile: experiment-profile-trace   \
                    experiment-profile-analyze

################################################################################
## experiment/profile/trace
################################################################################

define PROFILE_TRACE_CODE
result <- envtracer::trace_file('{1}');
experimentr::write_tracing_result(result, '$(EXPERIMENT_PROFILE_TRACE)/{1}/{2}/{3}')
endef

experiment-profile-trace: experiment-profile-example  \
                          experiment-profile-vignette \
                          experiment-profile-test     \
                          experiment-profile-testthat

define EXPERIMENT_PROFILE_TRACE_INDEX_CODE
library(experimentr);
invisible(select_packages(rank = 1:100, corpusfile='$(EXPERIMENT_PROFILE_TRACE_INDEX_CORPUS_FILEPATH)', clientfile='$(EXPERIMENT_PROFILE_TRACE_INDEX_CLIENT_FILEPATH)'));
invisible(tracing_index('$(EXPERIMENT_CORPUS_EXTRACT_INDEX_FILEPATH)', '$(EXPERIMENT_CORPUS_EXTRACT_PROGRAMS_DIRPATH)', '$(EXPERIMENT_PROFILE_TRACE_PROGRAMS_DIRPATH)', '$(EXPERIMENT_PROFILE_TRACE_INDEX_PROGRAMS_FILEPATH)', '$(EXPERIMENT_PROFILE_TRACE_INDEX_LOGDIR_FILEPATH)',
                          packages = readr::read_lines('$(EXPERIMENT_PROFILE_TRACE_INDEX_CORPUS_FILEPATH)'),
                          test_wrapper = 'library(envtracer)\ntrace <- trace_expr({{\n{code}\n}})\nlibrary(experimentr)\nwrite_trace(trace, \'{outdir}\')',
                          testthat_wrapper = 'library(envtracer)\ntrace <- trace_expr(testthat::test_file(\'{file}\', package=\'{package}\'))\nlibrary(experimentr)\nwrite_trace(trace, \'{outdir}\')',
                          example_wrapper = 'library(envtracer)\ntrace <- trace_expr({{\n{code}\n}})\nlibrary(experimentr)\nwrite_trace(trace, \'{outdir}\')',
                          vignette_wrapper = 'library(envtracer)\ntrace <- trace_expr({{\n{code}\n}})\nlibrary(experimentr)\nwrite_trace(trace, \'{outdir}\')'));
endef

experiment-profile-trace-index:
	mkdir -p $(EXPERIMENT_PROFILE_TRACE_INDEX_DIRPATH)
	mkdir -p $(EXPERIMENT_PROFILE_TRACE_PROGRAMS_DIRPATH)
	mkdir -p $(LOGS_PROFILE_TRACE_DIRPATH)
	$(call dockr_rdyntrace, "$(subst $(newline), ,$(EXPERIMENT_PROFILE_TRACE_INDEX_CODE))", $(EXPERIMENT_PROFILE_TRACE_INDEX_DIRPATH)/log)


experiment-profile-trace-programs:
	mkdir -p $(EXPERIMENT_PROFILE_TRACE_PROGRAMS_DIRPATH)
	time $(call dockr_parallel, --joblog $(EXPERIMENT_PROFILE_TRACE_PROGRAMS_JOBLOG_FILEPATH)  $(PARALLEL_ARGS) --results {1}/ $(R_DYNTRACE_BIN) --file={1}/program.R :::: $(EXPERIMENT_PROFILE_TRACE_INDEX_LOGDIR_FILEPATH))


experiment-profile-analyze: experiment-profile-reduce    \
                            experiment-profile-summarize

experiment-profile-reduce:
	$(shell find $(EXPERIMENT_PROFILE_TRACE_PROGRAMS_DIRPATH) -mindepth 3 -maxdepth 3 -type d > $(EXPERIMENT_PROFILE_TRACE_INDEX_DIRPATH)/reduce-index)
	time $(call dockr_parallel, --joblog $(EXPERIMENT_PROFILE_REDUCE_PROGRAMS_JOBLOG_FILEPATH) $(PARALLEL_ARGS) --results {1}/reduce/ $(R_VANILLA_BIN) --file=$(ANALYSIS_PROFILE_SCRIPT) --args reduce {1} {1}/reduce $(ANALYSIS) :::: $(EXPERIMENT_PROFILE_TRACE_INDEX_DIRPATH)/reduce-index)


experiment-profile-combine:
	mkdir -p $(EXPERIMENT_PROFILE_COMBINE_DIRPATH)
	time $(call dockr_rvanilla_file, $(ANALYSIS_PROFILE_SCRIPT) --slave --args combine $(EXPERIMENT_PROFILE_TRACE_PROGRAMS_DIRPATH) $(EXPERIMENT_PROFILE_COMBINE_DIRPATH) $(ANALYSIS), $(EXPERIMENT_PROFILE_COMBINE_DIRPATH)/log)

experiment-profile-summarize:
	mkdir -p $(EXPERIMENT_PROFILE_SUMMARIZE_DIRPATH)
	time $(call dockr_rvanilla_file, $(ANALYSIS_PROFILE_SCRIPT) --slave --args summarize $(EXPERIMENT_PROFILE_COMBINE_DIRPATH) $(EXPERIMENT_PROFILE_SUMMARIZE_DIRPATH) $(ANALYSIS), $(EXPERIMENT_PROFILE_SUMMARIZE_DIRPATH)/log)

experiment-profile-signature:
	mkdir -p $(EXPERIMENT_PROFILE_SIGNATURE_DIRPATH)
	time docker run $(DOCKR_RUN_ARGS) dockr $(R_VANILLA_BIN) --slave --file=$(ANALYSIS_SIGNATURE_SCRIPT) --args $(EXPERIMENT_PROFILE_SUMMARIZE_DIRPATH)/parameters.fst $(EXPERIMENT_PROFILE_TRACE_INDEX_CORPUS_FILEPATH) $(EXPERIMENT_PROFILE_SIGNATURE_DIRPATH)

################################################################################
## Experiment: Validate
################################################################################
experiment-validate: experiment-validate-trace-index     \
                     experiment-validate-trace-programs

define EXPERIMENT_VALIDATE_TRACE_INDEX_CODE
library(experimentr);
invisible(tracing_index('$(EXPERIMENT_CORPUS_EXTRACT_INDEX_FILEPATH)', '$(EXPERIMENT_CORPUS_EXTRACT_PROGRAMS_DIRPATH)', '$(EXPERIMENT_VALIDATE_TRACE_PROGRAMS_DIRPATH)', '$(EXPERIMENT_VALIDATE_TRACE_INDEX_PROGRAMS_FILEPATH)', '$(EXPERIMENT_VALIDATE_TRACE_INDEX_LOGDIR_FILEPATH)',
                          packages = readr::read_lines('$(EXPERIMENT_VALIDATE_TRACE_INDEX_CLIENT_FILEPATH)'),
                          test_wrapper = 'strictr::initialize_strictr(commandArgs(trailingOnly=TRUE)[[1]], commandArgs(trailingOnly=TRUE)[[2]])\n{code}\nstrictr::finalize_strictr(commandArgs(trailingOnly=TRUE)[[1]], commandArgs(trailingOnly=TRUE)[[2]], fst::write_fst)',
                          testthat_wrapper = 'strictr::initialize_strictr(commandArgs(trailingOnly=TRUE)[[1]], commandArgs(trailingOnly=TRUE)[[2]])\ntestthat::test_file(\'{file}\', package=\'{package}\')\nstrictr::finalize_strictr(commandArgs(trailingOnly=TRUE)[[1]], commandArgs(trailingOnly=TRUE)[[2]], fst::write_fst)',
                          example_wrapper = 'strictr::initialize_strictr(commandArgs(trailingOnly=TRUE)[[1]], commandArgs(trailingOnly=TRUE)[[2]])\n{code}\nstrictr::finalize_strictr(commandArgs(trailingOnly=TRUE)[[1]], commandArgs(trailingOnly=TRUE)[[2]], fst::write_fst)',
                          vignette_wrapper = 'strictr::initialize_strictr(commandArgs(trailingOnly=TRUE)[[1]], commandArgs(trailingOnly=TRUE)[[2]])\n{code}\nstrictr::finalize_strictr(commandArgs(trailingOnly=TRUE)[[1]], commandArgs(trailingOnly=TRUE)[[2]], fst::write_fst)'));
endef

experiment-validate-trace-index:
	mkdir -p $(EXPERIMENT_VALIDATE_TRACE_INDEX_DIRPATH)
	mkdir -p $(EXPERIMENT_VALIDATE_TRACE_PROGRAMS_DIRPATH)
	mkdir -p $(LOGS_VALIDATE_TRACE_DIRPATH)
	$(call dockr_rvanilla, "$(subst $(newline), ,$(EXPERIMENT_VALIDATE_TRACE_INDEX_CODE))", $(EXPERIMENT_VALIDATE_TRACE_INDEX_DIRPATH)/log)

experiment-validate-trace-programs:
	mkdir -p $(EXPERIMENT_VALIDATE_TRACE_PROGRAMS_DIRPATH)
	mkdir -p $(EXPERIMENT_VALIDATE_TRACE_PROGRAMS_JOBLOG_DIRPATH)
	$(call dockr_parallel, --joblog $(EXPERIMENT_VALIDATE_TRACE_PROGRAMS_JOBLOG_DIRPATH)/$(SIGNATURE)  $(PARALLEL_ARGS) --results {1}/$(SIGNATURE)/ $(R_VANILLA_BIN) --slave --file={1}/program.R --args {1} $(SIGNATURE) "2>&1" :::: $(EXPERIMENT_VALIDATE_TRACE_INDEX_LOGDIR_FILEPATH))

experiment-validate-trace-programs-all:
	-make experiment-validate-trace-programs TIMEOUT=300 SIGNATURE=lazy-1
	-make experiment-validate-trace-programs TIMEOUT=300 SIGNATURE=lazy-2
	-make experiment-validate-trace-programs TIMEOUT=300 SIGNATURE=signature+force+effect+reflection
	-make experiment-validate-trace-programs TIMEOUT=300 SIGNATURE=signature+force+effect-reflection
	-make experiment-validate-trace-programs TIMEOUT=300 SIGNATURE=signature+force-effect+reflection
	-make experiment-validate-trace-programs TIMEOUT=300 SIGNATURE=signature+force-effect-reflection
	-make experiment-validate-trace-programs TIMEOUT=300 SIGNATURE=signature-force+effect+reflection
	-make experiment-validate-trace-programs TIMEOUT=300 SIGNATURE=signature-force+effect-reflection
	-make experiment-validate-trace-programs TIMEOUT=300 SIGNATURE=signature-force-effect+reflection
	-make experiment-validate-trace-programs TIMEOUT=300 SIGNATURE=signature-force-effect-reflection

experiment-validate-retrace-programs:
	$(call dockr_parallel, --resume-failed --joblog $(EXPERIMENT_VALIDATE_TRACE_PROGRAMS_JOBLOG_DIRPATH)/$(SIGNATURE)  $(PARALLEL_ARGS) --results {1}/$(SIGNATURE)/ $(R_VANILLA_BIN) --slave --file={1}/program.R --args {1} $(SIGNATURE) "2>&1" :::: $(EXPERIMENT_VALIDATE_TRACE_INDEX_LOGDIR_FILEPATH))

experiment-validate-retrace-programs-all:
	-make experiment-validate-retrace-programs TIMEOUT=3000 SIGNATURE=lazy-1
	-make experiment-validate-retrace-programs TIMEOUT=3000 SIGNATURE=lazy-2
	-make experiment-validate-retrace-programs TIMEOUT=3000 SIGNATURE=signature+force+effect+reflection
	-make experiment-validate-retrace-programs TIMEOUT=3000 SIGNATURE=signature+force+effect-reflection
	-make experiment-validate-retrace-programs TIMEOUT=3000 SIGNATURE=signature+force-effect+reflection
	-make experiment-validate-retrace-programs TIMEOUT=3000 SIGNATURE=signature+force-effect-reflection
	-make experiment-validate-retrace-programs TIMEOUT=3000 SIGNATURE=signature-force+effect+reflection
	-make experiment-validate-retrace-programs TIMEOUT=3000 SIGNATURE=signature-force+effect-reflection
	-make experiment-validate-retrace-programs TIMEOUT=3000 SIGNATURE=signature-force-effect+reflection
	-make experiment-validate-retrace-programs TIMEOUT=3000 SIGNATURE=signature-force-effect-reflection



experiment-validate-run-program:
	docker run -i $(DOCKR_RUN_ARGS) dockr $(R_VANILLA_BIN) --debugger=gdb --file=$(EXPERIMENT_VALIDATE_TRACE_PROGRAMS_DIRPATH)/$(TYPE)/$(PACKAGE)/$(FILENAME)/program.R --args $(EXPERIMENT_VALIDATE_TRACE_PROGRAMS_DIRPATH)/$(TYPE)/$(PACKAGE)/$(FILENAME) $(SIGNATURE)


experiment-validate-summary:
	mkdir -p $(EXPERIMENT_VALIDATE_SUMMARY_DIRPATH)
	docker run -i $(DOCKR_RUN_ARGS) dockr $(R_VANILLA_BIN) --file=$(ANALYSIS_VALIDATE_SCRIPT) --args $(EXPERIMENT_VALIDATE_TRACE_PROGRAMS_DIRPATH) $(EXPERIMENT_VALIDATE_TRACE_PROGRAMS_JOBLOG_DIRPATH) $(EXPERIMENT_VALIDATE_SUMMARY_DIRPATH)

################################################################################
## experiment/report
################################################################################
experiment-report: experiment-report-paper  \
                   experiment-report-input  \
                   experiment-report-update \
                   experiment-report-render

################################################################################
## experiment/report/paper
################################################################################
experiment-report-paper:
	@mkdir -p $(EXPERIMENT_REPORT_DIRPATH)
	@mkdir -p $(LOGS_REPORT_PAPER_DIRPATH)
	$(call clonepull, $(PAPER_BRANCH), $(PAPER_GIT_URL), $(EXPERIMENT_REPORT_PAPER_DIRPATH), $(LOGS_REPORT_PAPER_DIRPATH)/clone.log)

################################################################################
## experimentr/report/input
################################################################################
experiment-report-input:
	mkdir -p $(EXPERIMENT_REPORT_PAPER_DATA_DIRPATH)
	mkdir -p $(LOGS_REPORT_INPUT_DIRPATH)
	cp $(EXPERIMENT_CORPUS_EXTRACT_INDEX_FILEPATH)  $(EXPERIMENT_REPORT_PAPER_DATA_DIRPATH)/extract-index.fst
	cp $(EXPERIMENT_CORPUS_SLOC_CORPUS_FILEPATH)  $(EXPERIMENT_REPORT_PAPER_DATA_DIRPATH)/sloc-corpus.fst
	cp $(EXPERIMENT_CORPUS_SLOC_PACKAGE_FILEPATH)  $(EXPERIMENT_REPORT_PAPER_DATA_DIRPATH)/sloc-package.fst
	cp $(EXPERIMENT_CORPUS_PACKAGE_INFO_FILEPATH) $(EXPERIMENT_REPORT_PAPER_DATA_DIRPATH)/package-info.fst

################################################################################
## experiment/report/render
################################################################################

experiment-report-render:
	mkdir -p $(LOGS_REPORT_RENDER_DIRPATH)
	$(call dockr_make, -C $(EXPERIMENT_REPORT_PAPER_DIRPATH) report R=$(R_DYNTRACE_BIN), $(LOGS_REPORT_RENDER_DIRPATH)/render.log)

################################################################################
## experiment/report/update
################################################################################

experiment-report-update:
	mkdir -p $(EXPERIMENT_REPORT_PAPER_DATA_DIRPATH)
	mkdir -p $(LOGS_REPORT_UPDATE_DIRPATH)
	$(call tee, git -C $(EXPERIMENT_REPORT_PAPER_DIRPATH) add *.fst *.html, $(LOGS_REPORT_UPDATE_DIRPATH)/add.log)
	$(call tee, git -C $(EXPERIMENT_REPORT_PAPER_DIRPATH) diff-index --quiet HEAD || git -C $(EXPERIMENT_REPORT_PAPER_DIRPATH) commit -m "Update data from $(shell hostname) on $(DATE)", $(LOGS_REPORT_UPDATE_DIRPATH)/commit.log)
	$(call tee, git -C $(EXPERIMENT_REPORT_PAPER_DIRPATH) push origin $(PAPER_BRANCH), $(LOGS_REPORT_UPDATE_DIRPATH)/push.log)

#parallelize( r_expr("experimentr::get_package_info('{}', index_filepath = '/tmp/{}.fst')"), vector_input(installed.packages()[,1]) )
#parallelize( r_file("{1}"), vector_input(dir_ls(glob = "*.R", recurse = TRUE)),  "--wd ...")
