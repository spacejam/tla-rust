------------------------------- MODULE pcal_intro -------------------------------
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10,
          account_total = alice_account + bob_account

process TransProc \in 1..2
  variables money \in 1..20;
begin
Transfer:
  if alice_account >= money then
     alice_account := alice_account - money;
       bob_account := bob_account + money;
  end if;
C: assert alice_account >= 0;
end process

end algorithm *)

\* generated TLA will go here

MoneyInvariant == alice_account + bob_account = account_total

=============================================================================
