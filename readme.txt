Things to do:
1. no aborting while error reporting.
2. class hierarchy
3. typecasting into child class, instead of virtual void


Observations in errors:
1. seg fault if undeclared real var is in RHS.
2. internal error(61,ast-build.cc) if exp_var undeclared when in RHS.
3. internal error(61,ast-build.cc) if type mismatch in * if a(float) = b(float) * c(int)



changes:
373, 350, 327, 307
