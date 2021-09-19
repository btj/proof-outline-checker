echo 'Require Import type_checker proof_checker. Require Extraction. Extraction "proof_checker.ml" post_env_of_stmt is_valid_proof_outline.' | coqtop -R . proofchecker
