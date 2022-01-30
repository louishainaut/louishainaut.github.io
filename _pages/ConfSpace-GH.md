---
title: "Configuration spaces on a wedge of spheres
permalink: /ConfSpace-GH-data/
author_profile: true

<script src="https://sagecell.sagemath.org/static/embedded_sagecell.js"></script>
<script>sagecell.makeSagecell({"inputLocation": ".sage", linked: 'True'});</script>
<script src="https://polyfill.io/v3/polyfill.min.js?features=es6"></script>
<script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
---

**Background**
This page contains the code necessary to compute the lower bounds to the compactly supported cohomology of configuration spaces on a wedge of spheres. Up to n=10 there is the
possibility to add the missing terms in order to have the full cohomology. For larger values of n it is only possible to compute the multiplicity of the symmetric and alternate powers.
Please check out the paper for more detail.

**Data presentation**
The cell below contains the functions necessary for computing the cohomology groups

<div class="sage">
    <script type="text/x-sage">
    ######################### Computations for the E1-page ################################

    p = SymmetricFunctions(QQ).power()
    s = SymmetricFunctions(QQ).schur()


    # returns the decomposition of the term in degree n of the Lie operad into irreducibles
    def Lie(n):
        if n == 0:
            return s.zero()

        result = sum(moebius(d)*p[d]^Integer(n/d) for d in divisors(n))
        return s(result/n)

    # This function and the next one implement by hand the plethysm of s[n] with SLie \otimes H_c(X), so that only the
    # necessary terms are computed and are added to the appropriate term on the E1 page
    def aux_func(part, chain_comp):
        l = part.to_exp()
        return prod( s[l[i]].plethysm(chain_comp[i+1]) for i in range(len(l)) )


    def E1(particles, dimension, line, col, CTot):
        result = s.zero().tensor(s.zero())
        for k in range(particles-line-col, particles-line+1):
            for part1 in Partitions(particles-k, length = line):
                temp_top = aux_func(part1, CTot[1])
                for part2 in Partitions(k, length = particles-line-col):
                    temp = aux_func(part2, CTot[0])*temp_top
                    result += temp
        return (-1)^(dimension*line+col)*result

    ############################## Computations for the E2-page ######################################

    # Takes the alternating sum of a line and distributes the terms in the two possibly non-zero terms according to
    # their sign (would provide the correct answer if there were no cancellation in the Euler characteristic)
    def Compute_LowerBound(particles, dimension):
        bound = particles+1

        # Returns the tensor product of SLie with the cohomology of X, graded by the degree of the cohomology part
        # The sign is chosen according to the degree of the corresponding term in the tensor product, so that Koszul
        # duality is automatically implemented
        CTot = [[-Lie(i).degree_negation().omega().tensor(s.one()) for i in range(bound)],
                [(-1)^(dimension+1)*Lie(i).degree_negation().omega().tensor(s[1]) for i in range(bound)]]

        if particles == 1:
            return[[E1(particles, dimension, 0, 0, CTot)], [E1(particles, dimension, 1, 0, CTot)]] # Since F(X, 1) = X

        #else:
        Hom = [[s.zero().tensor(s.zero())],[s.zero().tensor(s.zero())]]

        for line in range(1, particles):
            alt_sum = sum((-1)^(line+col+particles)*E1(particles, dimension, line, col, CTot) 
                          for col in range(particles-line+1))
            Hom[0].append(alt_sum.map_coefficients(lambda coeff : max(0, -coeff)))
            Hom[1].append(alt_sum.map_coefficients(lambda coeff : max(0, coeff)))

        Hom[1].append(E1(particles, dimension, particles, 0, CTot))
        return Hom


    ##The following is a long function. Therefore it is the last one on this cell

    # When Partial is set to True it only corrects the multiplicities whose value follows from a theoretical argument
    # (i.e. the symmetric and exterior powers).
    # When Partial is set to False it additionnally corrects the multiplicities according to specific computations
    def Sharpen_LowerBound(particles, dimension, Hom, Partial = False):
        if dimension%2 == 1:
            # Finds the correct multiplicity for the symmetric and exterior powers
            for n in range(1, particles):
                error = s.zero() + Focus_GL(Hom[0][n-1], [n-1]) - Focus_GL(Hom[1][n], [n])
                Hom[0][n] += error.tensor(s[n])
                Hom[1][n] += error.tensor(s[n])

            for n in range(2, particles):
                error = s.zero() + Focus_GL(Hom[0][n-2], [1]*(n-2)) - Focus_GL(Hom[1][n], [1]*n)
                Hom[0][n] += error.tensor(s[n].omega())
                Hom[1][n] += error.tensor(s[n].omega())

            if Partial:
                return Hom

            #else:
            # Adds corrections to the remaining Schur functors if there are no more than 10 particles
            if particles == 7:
                error = s[4,2,1].tensor(s[2,1])
                Hom[0][3] += error
                Hom[1][3] += error

            if particles == 8:
                error = (2*s[5,2,1] + s[4,3,1] + s[4,2,2] + s[4,2,1,1] + s[3,3,1,1] + s[3,2,2,1]).tensor(s[2,1])
                Hom[0][3] += error
                Hom[1][3] += error
                error = s[6,2].tensor(s[2,1,1])
                Hom[0][4] += error
                Hom[1][4] += error

            if particles == 9:
                error = (s[6,3] + 2*s[6,2,1] + s[6,1,1,1] + 2*s[5,3,1] + s[5,2,2] + 3*s[5,2,1,1]).tensor(s[2,1])
                error += (2*s[4,4,1] + 3*s[4,3,2] + 4*s[4,3,1,1] + 4*s[4,2,2,1] + 3*s[4,2,1,1,1]).tensor(s[2,1])
                error += (2*s[3,3,2,1] + s[3,3,1,1,1] + s[3,2,2,2] + 2*s[3,2,2,1,1]).tensor(s[2,1])
                Hom[0][3] += error
                Hom[1][3] += error
                error = (s[7,2] + s[5,2,2] + s[4,4,1] + s[3,2,2,2]).tensor(s[3,1])
                error += (s[6,2,1] + s[5,3,1]).tensor(s[2,1,1])
                Hom[0][4] += error
                Hom[1][4] += error
                error = s[7,2].tensor(s[2,1,1,1])
                Hom[0][5] += error
                Hom[1][5] += error

            if particles == 10: 
                #Schur functor [2,1]
                error = s[7,3] + 2*s[7,2,1] + s[7,1,1,1] + s[6,4] + 5*s[6,3,1] + 2*s[6,2,2] + 5*s[6,2,1,1] + s[6,1,1,1,1]
                error += 4*s[5,4,1] + 6*s[5,3,2] + 9*s[5,3,1,1] + 7*s[5,2,2,1] + 6*s[5,2,1,1,1] + s[5,1,1,1,1,1]
                error += 3*s[4,4,2] + 4*s[4,4,1,1] + 4*s[4,3,3] + 10*s[4,3,2,1] + 7*s[4,3,1,1,1] + 4*s[4,2,2,2]
                error += 9*s[4,2,2,1,1] + 3*s[4,2,1,1,1,1] + 2*s[3,3,3,1] + 3*s[3,3,2,2] + 6*s[3,3,2,1,1]
                error += 2*s[3,3,1,1,1,1] + 3*s[3,2,2,2,1] + 3*s[3,2,2,1,1,1] + s[2,2,2,2,1,1]
                Hom[0][3] += error.tensor(s[2,1])
                Hom[1][3] += error.tensor(s[2,1])
                #Schur functor [3,1]
                error = s[7,2,1] + 2*s[6,3,1] + s[6,2,1,1] + s[5,4,1] + s[5,3,2] + 2*s[5,3,1,1] + s[5,2,2,1] + s[4,4,2]
                error += s[4,3,3] + 2*s[4,3,2,1] + s[4,2,2,2] + s[4,2,2,1,1] + s[3,3,2,1,1] + s[3,2,2,2,1]
                Hom[0][4] += error.tensor(s[3,1])
                Hom[1][4] += error.tensor(s[3,1])
                #Schur functor [2,2]
                error = s[4,4,2]
                Hom[0][4] += error.tensor(s[2,2])
                Hom[1][4] += error.tensor(s[2,2])
                #Schur functor [2,1,1]
                error = s[8,1,1] + s[7,3] + s[7,2,1] + s[7,1,1,1] + 2*s[6,3,1] + 2*s[6,2,1,1] + s[5,4,1] + s[5,3,2] + s[5,3,1,1]
                error += s[5,2,2,1] + s[4,4,1,1] + s[4,3,3]
                Hom[0][4] += error.tensor(s[2,1,1])
                Hom[1][4] += error.tensor(s[2,1,1])
                #Schur functor [3,1,1]
                error = s[8,2]
                Hom[0][5] += error.tensor(s[3,1,1])
                Hom[1][5] += error.tensor(s[3,1,1])
                #Schur functor [2,1,1,1]
                error = s[7,2,1] + s[6,3,1]
                Hom[0][5] += error.tensor(s[2,1,1,1])
                Hom[1][5] += error.tensor(s[2,1,1,1])
                #Schur functor [2,1^4]
                error = s[8,2]
                Hom[0][6] += error.tensor(s([2]+[1]*4))
                Hom[1][6] += error.tensor(s([2]+[1]*4))

            return Hom

        else: #if dimension%2 == 0:
            # Finds the correct multiplicity for the symmetric and exterior powers
            for n in range(2, particles):
                error = s.zero() + Focus_GL(Hom[0][n-2], [n-2]) - Focus_GL(Hom[1][n], [n])
                Hom[0][n] += error.tensor(s[n])
                Hom[1][n] += error.tensor(s[n])

            for n in range(1, particles):
                error = s.zero() + Focus_GL(Hom[0][n-1], [1]*(n-1)) - Focus_GL(Hom[1][n], [1]*n)
                Hom[0][n] += error.tensor(s[n].omega())
                Hom[1][n] += error.tensor(s[n].omega())

            if Partial:
                return Hom

            #else:
            # Adds corrections to the remaining Schur functors if there are no more than 10 particles
            if particles == 7:
                error = s[4,2,1].tensor(s[2,1])
                Hom[0][3] += error
                Hom[1][3] += error

            if particles == 8:
                error = (2*s[5,2,1] + s[4,3,1] + s[4,2,2] + s[4,2,1,1] + s[3,3,1,1] + s[3,2,2,1]).tensor(s[2,1])
                Hom[0][3] += error
                Hom[1][3] += error
                error = s[6,2].tensor(s[3,1])
                Hom[0][4] += error
                Hom[1][4] += error

            if particles == 9:
                error = (s[6,3] + 2*s[6,2,1] + s[6,1,1,1] + 2*s[5,3,1] + s[5,2,2] + 3*s[5,2,1,1] + 2*s[4,4,1] + 3*s[4,3,2] + 4*s[4,3,1,1] + 4*s[4,2,2,1] + 3*s[4,2,1,1,1] + 2*s[3,3,2,1] + s[3,3,1,1,1] + s[3,2,2,2] + 2*s[3,2,2,1,1]).tensor(s[2,1])
                Hom[0][3] += error
                Hom[1][3] += error
                error = (s[7,2] + s[5,2,2] + s[4,4,1] + s[3,2,2,2]).tensor(s[2,1,1])
                error += (s[6,2,1] + s[5,3,1]).tensor(s[3,1])
                Hom[0][4] += error
                Hom[1][4] += error
                error = s[7,2].tensor(s[4,1])
                Hom[0][5] += error
                Hom[1][5] += error

            if particles == 10: 
                #Schur functor [2,1]
                error = s[7,3] + 2*s[7,2,1] + s[7,1,1,1] + s[6,4] + 5*s[6,3,1] + 2*s[6,2,2] + 5*s[6,2,1,1] + s[6,1,1,1,1]
                error += 4*s[5,4,1] + 6*s[5,3,2] + 9*s[5,3,1,1] + 7*s[5,2,2,1] + 6*s[5,2,1,1,1] + s[5,1,1,1,1,1]
                error += 3*s[4,4,2] + 4*s[4,4,1,1] + 4*s[4,3,3] + 10*s[4,3,2,1] + 7*s[4,3,1,1,1] + 4*s[4,2,2,2]
                error += 9*s[4,2,2,1,1] + 3*s[4,2,1,1,1,1] + 2*s[3,3,3,1] + 3*s[3,3,2,2] + 6*s[3,3,2,1,1]
                error += 2*s[3,3,1,1,1,1] + 3*s[3,2,2,2,1] + 3*s[3,2,2,1,1,1] + s[2,2,2,2,1,1]
                Hom[0][3] += error.tensor(s[2,1])
                Hom[1][3] += error.tensor(s[2,1])
                #Schur functor [3,1]
                error = s[8,1,1] + s[7,3] + s[7,2,1] + s[7,1,1,1] + 2*s[6,3,1] + 2*s[6,2,1,1] + s[5,4,1] + s[5,3,2] + s[5,3,1,1]
                error += s[5,2,2,1] + s[4,4,1,1] + s[4,3,3]
                Hom[0][4] += error.tensor(s[3,1])
                Hom[1][4] += error.tensor(s[3,1])
                #Schur functor [2,2]
                error = s[4,4,2]
                Hom[0][4] += error.tensor(s[2,2])
                Hom[1][4] += error.tensor(s[2,2])
                #Schur functor [2,1,1]
                error = s[7,2,1] + 2*s[6,3,1] + s[6,2,1,1] + s[5,4,1] + s[5,3,2] + 2*s[5,3,1,1] + s[5,2,2,1] + s[4,4,2]
                error += s[4,3,3] + 2*s[4,3,2,1] + s[4,2,2,2] + s[4,2,2,1,1] + s[3,3,2,1,1] + s[3,2,2,2,1]
                Hom[0][4] += error.tensor(s[2,1,1])
                Hom[1][4] += error.tensor(s[2,1,1])
                #Schur functor [4,1]
                error = s[7,2,1] + s[6,3,1]
                Hom[0][5] += error.tensor(s[4,1])
                Hom[1][5] += error.tensor(s[4,1])
                #Schur functor [3,1,1]
                error = s[8,2]
                Hom[0][5] += error.tensor(s[3,1,1])
                Hom[1][5] += error.tensor(s[3,1,1])
                #Schur functor [5,1]
                error = s[8,2]
                Hom[0][6] += error.tensor(s[5,1])
                Hom[1][6] += error.tensor(s[5,1])

            return Hom

    print('Success!')
    </script>
</div>
