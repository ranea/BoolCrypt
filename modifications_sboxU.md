# Modifying sboxU for BoolCrypt

BoolCrypt requires to adapt [sboxU](https://github.com/lpp-crypto/sboxU) to include
two additional functions `all_linear_equivalences_fast` and `number_linear_equivalences`.
The steps to modify *sboxU* are the following:

1. Include in `sboxu_cpp.pxd`:

```
cdef extern from "sboxu_cpp_equiv.hpp" :
    [...]
    cdef vector[ vector[uint64_t] ] all_linear_equivalences_cpp(const vector[uint64_t] f, const vector[uint64_t] g);
    cdef uint64_t number_linear_equivalences_cpp(const vector[uint64_t] l0, const vector[uint64_t] l1);
```


2. Include in `sboxu_cpp_equiv.hpp`:

```
std::vector<Sbox> all_linear_equivalences_cpp(const Sbox f, const Sbox g);
unsigned int number_linear_equivalences_cpp(const Sbox l0, const Sbox l1);
```

3. Include in `cpp_equiv.pyx`:

```
def all_linear_equivalences_fast(l0, l1):
	return all_linear_equivalences_cpp(l0, l1)

def number_linear_equivalences(l0, l1):
	return number_linear_equivalences_cpp(l0, l1)
```


4. Include in `sboxu_cpp_equiv.cpp`:
 
```
// each two elements in the vector returned is a SE
std::vector<Sbox> all_linear_equivalences_cpp(const Sbox f, const Sbox g)
{
    check_length_cpp(f);
    check_length_cpp(g);
    std::vector<Sbox> result;
    // if f(0) == 0 then it is necessary that g(0) == 0...
    if ((f[0] == 0) and (g[0] != 0))
        return result;
    // ... and vice-versa
    else if ((f[0] != 0) and (g[0] == 0))
        return result;
    // We look for A,B such that f = B o g o A
    Sbox f_inv = inverse_cpp(f), g_inv = inverse_cpp(g);
    std::vector<IOpair> constraints;
    if (f[0] != 0)
    {                           // in this case, we know that B(g[0]) = f[0]
        constraints.push_back(IOpair(g[0], f[0]));
    }
    std::vector<LEguessIterator> b_generators;
    b_generators.push_back(LEguessIterator(f.size(), constraints));
    while (true)
    {
        while ((b_generators.size() > 0) and (not b_generators.back().prepare_successfully()))
            b_generators.pop_back();
        if (b_generators.size() == 0)  return result;
                // return std::vector<Sbox>(); // nothing to be found, we
                                            // have exhausted all
                                            // possible guesses
        LEguess
            a(f.size()),
            b = b_generators.back().get_prepared_guess();

        std::vector<IOpair> just_added, to_treat, next_to_treat;
        for (unsigned int x=0; x<f.size(); x++)
            if (b.is_entry_set(x))
                to_treat.push_back(IOpair(x, b.img(x)));
        bool
            conclusion_reached = false, // true if and only if we have
                                        // propagated the intial guess
                                        // as far as possible.
            contradiction_found = false; // true if and only if the
                                         // initial guess leads to
                                         // some inconsistency.
        // propagating the guess on B
        while (not conclusion_reached)
        {
            conclusion_reached = true;
            try
            {
                // B(y) = b_y => A(f_inv(b_y)) = g_inv(y)
                for (auto & entry : to_treat)
                {
                    BinWord y = entry.first, b_y = entry.second;
                    just_added = a.add_entry(IOpair(f_inv[b_y], g_inv[y]));
                    next_to_treat.insert(next_to_treat.end(),
                                         just_added.begin(),
                                         just_added.end());
                }
                to_treat = next_to_treat;
                next_to_treat.clear();
                if (to_treat.size() > 0)
                    conclusion_reached = false;
                // A(x) = a_x => B(g(a_x)) = f(x)
                for (auto & entry : to_treat)
                {
                    BinWord x = entry.first, a_x = entry.second;
                    just_added = b.add_entry(IOpair(g[a_x], f[x]));
                    next_to_treat.insert(next_to_treat.end(),
                                         just_added.begin(),
                                         just_added.end());
                }
                to_treat = next_to_treat;
                next_to_treat.clear();
                if (to_treat.size() > 0)
                    conclusion_reached = false;
            }
            catch (ContradictionFound & e)
            {
                conclusion_reached = true;
                contradiction_found = true;
            }
        }
        if (not contradiction_found)
        {
            if (not b.complete())
                // inconclusive: we will guess one more entry
                b_generators.push_back(b_generators.back().deeper_guess_gen());
            else
            {                   // we have everything we need
                // std::vector<Sbox> result;
                Sbox A(f.size(), 0), B(b.lut());
                if (is_permutation_cpp(B))
                {
                    Sbox B_inv(inverse_cpp(B));
                    // A is rebuilt from scratch using that f = B o g o A
                    for (unsigned int x=0; x<B.size(); x++)
                        A[x] = g_inv[B_inv[f[x]]];
                    result.push_back(A);
                    result.push_back(B);
                    // return result;
                }
                else
                    // inconclusive: we will guess one more entry
                    b_generators.push_back(b_generators.back().deeper_guess_gen());

            }
        }
    }
}



unsigned int number_linear_equivalences_cpp(const Sbox f, const Sbox g)
{
    check_length_cpp(f);
    check_length_cpp(g);
    unsigned int result = 0;
    // if f(0) == 0 then it is necessary that g(0) == 0...
    if ((f[0] == 0) and (g[0] != 0))
        return 0;
    // ... and vice-versa
    else if ((f[0] != 0) and (g[0] == 0))
        return 0;
    // We look for A,B such that f = B o g o A
    Sbox f_inv = inverse_cpp(f), g_inv = inverse_cpp(g);
    std::vector<IOpair> constraints;
    if (f[0] != 0)
    {                           // in this case, we know that B(g[0]) = f[0]
        constraints.push_back(IOpair(g[0], f[0]));
    }
    std::vector<LEguessIterator> b_generators;
    b_generators.push_back(LEguessIterator(f.size(), constraints));
    while (true)
    {
        while ((b_generators.size() > 0) and (not b_generators.back().prepare_successfully()))
            b_generators.pop_back();
        if (b_generators.size() == 0){
            return result;
        }
        LEguess
            a(f.size()),
            b = b_generators.back().get_prepared_guess();

        std::vector<IOpair> just_added, to_treat, next_to_treat;
        for (unsigned int x=0; x<f.size(); x++)
            if (b.is_entry_set(x))
                to_treat.push_back(IOpair(x, b.img(x)));
        bool
            conclusion_reached = false, // true if and only if we have
                                        // propagated the intial guess
                                        // as far as possible.
            contradiction_found = false; // true if and only if the
                                         // initial guess leads to
                                         // some inconsistency.
        // propagating the guess on B
        while (not conclusion_reached)
        {
            conclusion_reached = true;
            try
            {
                // B(y) = b_y => A(f_inv(b_y)) = g_inv(y)
                for (auto & entry : to_treat)
                {
                    BinWord y = entry.first, b_y = entry.second;
                    just_added = a.add_entry(IOpair(f_inv[b_y], g_inv[y]));
                    next_to_treat.insert(next_to_treat.end(),
                                         just_added.begin(),
                                         just_added.end());
                }
                to_treat = next_to_treat;
                next_to_treat.clear();
                if (to_treat.size() > 0)
                    conclusion_reached = false;
                // A(x) = a_x => B(g(a_x)) = f(x)
                for (auto & entry : to_treat)
                {
                    BinWord x = entry.first, a_x = entry.second;
                    just_added = b.add_entry(IOpair(g[a_x], f[x]));
                    next_to_treat.insert(next_to_treat.end(),
                                         just_added.begin(),
                                         just_added.end());
                }
                to_treat = next_to_treat;
                next_to_treat.clear();
                if (to_treat.size() > 0)
                    conclusion_reached = false;
            }
            catch (ContradictionFound & e)
            {
                conclusion_reached = true;
                contradiction_found = true;
            }
        }
        if (not contradiction_found)
        {
            if (not b.complete())
                // inconclusive: we will guess one more entry
                b_generators.push_back(b_generators.back().deeper_guess_gen());
            else
            {                   // we have everything we need
                // std::vector<Sbox> result;
                Sbox B(b.lut());
                if (is_permutation_cpp(B))
                {
                    result += 1;
                }
                else
                    // inconclusive: we will guess one more entry
                    b_generators.push_back(b_generators.back().deeper_guess_gen());

            }
        }
    }
}
```