---
title: "Compactly supported cohomology of configuration spaces on a wedge of spheres"
permalink: /ConfSpace-GH/
author_profile: true
---

<script src="https://sagecell.sagemath.org/static/embedded_sagecell.js"></script>
<script>sagecell.makeSagecell({"inputLocation": ".sage", linked: 'True'});</script>
<link rel="stylesheet" type="text/css" href="https://sagecell.sagemath.org/static/sagecell_embed.css">

{% include base_path %}

**[Background](#background)**
**[Data Presentation](#data)**

# Background {#background}

This page contains data from the paper *[Configuration spaces on a wedge of spheres and higher Hochschild homology](https://arxiv.org)*, by Nir Gadish and Louis Hainaut. Please check out our paper for more details.

# Data Presentation {#data}

The cell below contains the functions necessary to compute the cohomology. *(These cells are linked, so please always start with evaluating the first two cells.)*

<div class="sage">
<script type="text/x-sage">
    
{# Computations for the E1-page

p = SymmetricFunctions(QQ).power()
s = SymmetricFunctions(QQ).schur()

# returns the decomposition of the term in degree n of the Lie operad into irreducibles
def Lie(n):
    if n == 0:
        return s.zero()
        
    result = sum(moebius(d)*p[d]^Integer(n/d) for d in divisors(n))
    return s(result/n)

# This function and the next one implement by hand the plethysm of s[n] with SLie \otimes H(X), so that only the
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
    
# Computations for the E2-page

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


#The following is a long function. Therefore it is the last one on this cell

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
            error = (s[6,3] + 2*s[6,2,1] + s[6,1,1,1] + 2*s[5,3,1] + s[5,2,2] + 3*s[5,2,1,1] + 2*s[4,4,1] + 3*s[4,3,2] + 4*s[4,3,1,1] + 4*s[4,2,2,1] + 3*s[4,2,1,1,1] + 2*s[3,3,2,1] + s[3,3,1,1,1] + s[3,2,2,2] + 2*s[3,2,2,1,1]).tensor(s[2,1])
            Hom[0][3] += error
            Hom[1][3] += error
            error = (s[7,2] + s[5,2,2] + s[4,4,1] + s[3,2,2,2] + s[6,2,1] + s[5,3,1]).tensor(s[3,1])
            Hom[0][4] += error
            Hom[1][4] += error
            error = s[7,2].tensor(s[2,1,1,1])
            Hom[0][5] += error
            Hom[1][5] += error
            
        if particles == 10: 
            #Schur functor [2,1]
            error = s[7,3] + 2*s[7,2,1] + s[7,1,1,1] + s[6,4] + 5*s[6,3,1] + 2*s[6,2,2] + 5*s[6,2,1,1] + s[6,1,1,1,1] + 4*s[5,4,1] + 6*s[5,3,2] + 9*s[5,3,1,1] + 7*s[5,2,2,1] + 6*s[5,2,1,1,1] + s[5,1,1,1,1,1] + 3*s[4,4,2] + 4*s[4,4,1,1] + 4*s[4,3,3] + 10*s[4,3,2,1] + 7*s[4,3,1,1,1] + 4*s[4,2,2,2] + 9*s[4,2,2,1,1] + 3*s[4,2,1,1,1,1] + 2*s[3,3,3,1] + 3*s[3,3,2,2] + 6*s[3,3,2,1,1] + 2*s[3,3,1,1,1,1] + 3*s[3,2,2,2,1] + 3*s[3,2,2,1,1,1] + s[2,2,2,2,1,1]
            Hom[0][3] += error.tensor(s[2,1])
            Hom[1][3] += error.tensor(s[2,1])
            #Schur functor [3,1]
            error = s[7,2,1] + 2*s[6,3,1] + s[6,2,1,1] + s[5,4,1] + s[5,3,2] + 2*s[5,3,1,1] + s[5,2,2,1] + s[4,4,2] + s[4,3,3] + 2*s[4,3,2,1] + s[4,2,2,2] + s[4,2,2,1,1] + s[3,3,2,1,1] + s[3,2,2,2,1]
            Hom[0][4] += error.tensor(s[3,1])
            Hom[1][4] += error.tensor(s[3,1])
            #Schur functor [2,2]
            error = s[4,4,2]
            Hom[0][4] += error.tensor(s[2,2])
            Hom[1][4] += error.tensor(s[2,2])
            #Schur functor [2,1,1]
            error = s[8,1,1] + s[7,3] + s[7,2,1] + s[7,1,1,1] + 2*s[6,3,1] + 2*s[6,2,1,1] + s[5,4,1] + s[5,3,2] + s[5,3,1,1] + s[5,2,2,1] + s[4,4,1,1] + s[4,3,3]
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
            error = s[7,3] + 2*s[7,2,1] + s[7,1,1,1] + s[6,4] + 5*s[6,3,1] + 2*s[6,2,2] + 5*s[6,2,1,1] + s[6,1,1,1,1] + 4*s[5,4,1] + 6*s[5,3,2] + 9*s[5,3,1,1] + 7*s[5,2,2,1] + 6*s[5,2,1,1,1] + s[5,1,1,1,1,1] + 3*s[4,4,2] + 4*s[4,4,1,1] + 4*s[4,3,3] + 10*s[4,3,2,1] + 7*s[4,3,1,1,1] + 4*s[4,2,2,2] + 9*s[4,2,2,1,1] + 3*s[4,2,1,1,1,1] + 2*s[3,3,3,1] + 3*s[3,3,2,2] + 6*s[3,3,2,1,1] + 2*s[3,3,1,1,1,1] + 3*s[3,2,2,2,1] + 3*s[3,2,2,1,1,1] + s[2,2,2,2,1,1]
            Hom[0][3] += error.tensor(s[2,1])
            Hom[1][3] += error.tensor(s[2,1])
            #Schur functor [3,1]
            error = s[8,1,1] + s[7,3] + s[7,2,1] + s[7,1,1,1] + 2*s[6,3,1] + 2*s[6,2,1,1] + s[5,4,1] + s[5,3,2] + s[5,3,1,1] + s[5,2,2,1] + s[4,4,1,1] + s[4,3,3]
            Hom[0][4] += error.tensor(s[3,1])
            Hom[1][4] += error.tensor(s[3,1])
            #Schur functor [2,2]
            error = s[4,4,2]
            Hom[0][4] += error.tensor(s[2,2])
            Hom[1][4] += error.tensor(s[2,2])
            #Schur functor [2,1,1]
            error = s[7,2,1] + 2*s[6,3,1] + s[6,2,1,1] + s[5,4,1] + s[5,3,2] + 2*s[5,3,1,1] + s[5,2,2,1] + s[4,4,2] + s[4,3,3] + 2*s[4,3,2,1] + s[4,2,2,2] + s[4,2,2,1,1] + s[3,3,2,1,1] + s[3,2,2,2,1]
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
        
print("Success!")}
    
</script>
</div>
    
The following cell contains functions to help the visualization of the data produced.
    
<div class="sage">
    <script type="text/x-sage">
        
def Focus_Cohomology(Hom, Focus = "Sym", partition = None, codim = 1, Filtered = False):
    if Focus == "Sym":
        if Filtered:
            return [Focus_SymGroup(el, partition) for el in Hom[1-codim]]
        else:
            return Focus_SymGroup(sum(Hom[1-codim]), partition)
        
    if Focus == "GL":
        line = sum(partition)
        return Focus_GL(Hom[1-codim][line], partition)
    
def Forget_Equivariance(Hom, Forget = "Sym", genus = 0, codim = 1, Filtered = False):
    if Forget == "Sym":
        if Filtered:
            return [Forget_SymGroup(el) for el in Hom[1-codim]]
        else:
            return Forget_Symgroup(sum(Hom[1-codim]))
        
    if Forget == "GL":
        if genus <= 0:
            raise(ValueError("The variable 'genus' must be a positive integer"))
            
        if Filtered:
            return [Forget_GL(el, genus) for el in Hom[1-codim]]
        else:
            return Forget_GL(sum(Hom[1-codim]), genus)
        
def Restrict_Genus(Hom, genus):
    if genus <= 0:
        raise(ValueError("The variable 'genus' must be a positive integer"))
    
    return [[Restr_Genus(el, genus) for el in list_filtered] for list_filtered in Hom]
    

# Returns the equivariant cohomology of the moduli space M2n in weight zero
# 'codim' can only take two values. The default codim=1 outputs the cohomological degree n+2
# Alternatively the value codim=0 outputs the cohomological degree n+3
# By default this function first computes the homology of a wedge of circles. If this is
# already known it can be given as the input 'Hom'.
def Cohomology_M2n(particles, Hom = None, codim = 1):
    if Hom == None:
        Hom = Compute_LowerBound(particles, 1)
        Hom = Sharpen_LowerBound(particles, 1, Hom)
    
    result = s.zero()
    for n in range(particles+1-codim):
        for part in Partitions(n, max_length = 2):
            result += Twisted_Cohom_M2(part)*Focus_GL(Hom[1-codim][sum(part)], part)
            
    return result
  
# Helper functions, you should not need to call them directly
def Focus_GL(element, part):
    return sum(coeff*s[index[0]]*(index[1]==part) for index, coeff in element)
def Focus_SymGroup(element, part):
    return sum(coeff*s[index[1]]*(index[0]==part) for index, coeff in element)
def Forget_GL(element, genus):
    return sum(coeff*(s[index[1]].expand(genus)([1]*genus))*s[index[0]] for index, coeff in element)
def Forget_SymGroup(element):
    return sum(coeff*(Partition(index[0]).dimension())*s[index[1]] for index, coeff in element)
def Restr_Genus(element, genus):
    return element.map_item(lambda index, coeff: (index, coeff*(len(index[1]) <= genus)))
def trace_GL_irrep(part, eigenvalues):
    return s[part].expand(len(eigenvalues))(eigenvalues)
def Twisted_Cohom_M2(partition):
    if partition not in Partitions():
        raise ValueError("The parameter 'partition' must be a partition")
        
    if len(partition) > 2:
        return 0
    
    a = partition.get_part(0)
    b = partition.get_part(1)
    
    if (a+b)%2 == 1:
        return 0
    
    #else:
    return int((a - b)/6) + (a % 2)
print("Success!")
        
    </script>
</div>
    
The following cell contains examples of how to compute and display the cohomology of the configuration spaces. If you are only interested in the cohomology of $\mathcal{M}_{2,n}$ please see the last cell.
    
<div class = "sage">
    <script type="text/x-sage">
        
    </script>
</div>
    
    
<div class="sage"><script type="text/x-sage">
    M2n = Cohomology_M2n(10)
    # M2n = Cohomology_M2n(8, Hom = Already_Computed, codim = 0)
    # for part in Partitions(10):
    #    print(part, " : ", M2n.scalar(s(part)))

</script></div>
