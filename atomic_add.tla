------------------------------- MODULE atomic_add -------------------------------
EXTENDS Naturals

(* --algorithm atomic_add

\* Simple warmup for ensuring that the global_counter
\* always reaches an intended state.

variables global_counter = 0

process AdderProc \in 1..2
begin
Increment:
  global_counter := global_counter + 1;
end process

process Checker = 3
begin
Check:
    await global_counter = 2;
end process

end algorithm *)

=============================================================================
