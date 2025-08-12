procedure TSTAssertEQ(computed, expected)
  if computed eq expected then return; end if;
  assert false;
end procedure;

procedure TSTAssertNE(computed, expected)
  if computed ne expected then return; end if;
  assert false;
end procedure;

function TSTEvalList(f, args)
    n := #args;
    if n eq 0 then
        return f();
    elif n eq 1 then
        return f(args[1]);
    elif n eq 2 then
        return f(args[1], args[2]);
    elif n eq 3 then
        return f(args[1], args[2], args[3]);
    elif n eq 4 then
        return f(args[1], args[2], args[3], args[4]);
    else
        error "ApplyList only supports lists of length up to 4 (extend if needed)";
    end if;
end function;

procedure TSTAssertRaises(f, message, args, ...)
// example usage
// TSTAssertRaises(Factorization, "some_message", 0);
  try 
    TSTEvalList(f, args);
  catch err
    if message in err`Object then
      return;
    end if;
    printf "TST Failed: Error message: %o does not occur in:\n %o", message, err`Object;
    assert false;
  end try;
  printf "TST Failed: No error was raised by %O", f, "Minimal";
  assert false;
end procedure;
