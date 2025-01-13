'''
This document contains an algorithm to compute Theta(Q1, Q2), 
as defined in my msc thesis. 
Author: Felix Kalker

EXAMPLES: 
sage: Q1 = BinaryQF(1, 1, -1)
sage: Q2 = BinaryQF(1, 2, -1)
sage: Theta(Q1, Q2)
1

sage: Q1 = BinaryQF(1, 1, -1)
sage: Q2 = BinaryQF(2, 2, -1)
sage: Theta(Q1, Q2).minpoly()
x^2 + 147/11*x + 1

sage: Q1 = BinaryQF(4, 6, -7)
sage: Q2 = BinaryQF(7, 6, -10)
sage: f = Theta(Q1, Q2).minpoly()
sage: f *= lcm([ai.denominator() for ai in f.coefficients()])
sage: print(f)
1932404095170907030264359057729397827008726868759052041951451351988561892462708697*x^4 - 4306435258386914218036226884073702969386340275372644597995378230700574931870323193172025188*x^3 - 14335270990687861756254357363169891601512209118402872071205989182796448348557888969017462382942327018*x^2 + 1673185694775894168010946749258487874368640510237139298991336652824983124019268555005894812*x + 62611282959971165236114513553945184977289328158699272876446643264567685445748697
sage: f[0].factor()
3^3 * 7^2 * 17^2 * 19^2 * 29^2 * 73^3 * 101 * 107 * 139 * 181^2 * 269 * 271 * 379^2 * 419^2 * 433 * 761 * 1163 * 1381 * 1489 * 1601 * 3617 * 3889 * 8443 * 9091 * 11251

sage: class_group_representatives(136)
[5*x^2 + 4*x*y - 6*y^2,
 5*x^2 + 6*x*y - 5*y^2,
 2*x^2 + 8*x*y - 9*y^2,
 9*x^2 + 8*x*y - 2*y^2]

sage: for Q1 in class_group_representatives(148):
....:     for Q2 in class_group_representatives(316):
....:         if Theta(Q1, Q2) * Theta(Q2, Q1) != 1:
....:             print(Q1, Q2)
....: 
sage: 

sage: Q = BinaryQF(1, 1, -1)
sage: find_cycle(Q)
(
[x^2 + x*y - y^2, -x^2 + x*y + y^2],

[-x^2 + x*y + y^2, x^2 - x*y - y^2, x^2 + x*y - y^2, -x^2 - x*y + y^2],

[1 1]                     
[1 2], ' S T^-1 S T^1 S S'
)
sage: (1 * principal_root(Q) + 2).norm()
1
'''

def principal_root(Q):
    '''
    Returns the principal root (-b + sqrt(disc))/2a, represented as an element 
    of the number field K = Q(sqrt(disc)) with the embedding sqrt(disc) > 0
    '''
    a, b, c = Q
    disc = Q.discriminant()
    generator_name = 'sqrt' + str(disc)
    K = NumberField(x^2-disc, generator_name, embedding=RR(sqrt(disc)))
    sqrtdiscQ = K.gen()
    return((-b + sqrtdiscQ)/(2*a))

def other_root(Q):
    '''
    Returns the conjugate  (-b - sqrt(disc))/2a of the principal root, represented as an element 
    of the number field K = Q(sqrt(disc)) with the embedding sqrt(disc) > 0
    '''
    a, b, c = Q
    disc = Q.discriminant()
    generator_name = 'sqrt' + str(disc)
    K = NumberField(x^2-disc, generator_name, embedding=RR(sqrt(disc)))
    sqrtdiscQ = K.gen()
    return((-b - sqrtdiscQ)/(2*a))

def find_cycle(Q):
    '''
    Given a reduced binary form, with positive discriminant, find: 
    - the cycle of reduced forms, 
    - the cycle of nearly reduced forms, 
    - the automorph
    - the automorph written as a word in S and T

    See Appendix A of my master's thesis for an extensive explanation of this 
    algorithm. 
    
    INPUT: 
    - a reduced binary quadratic form Q = <a, b, c> (i.e. ac < 0 and b > |a + c|)
    
    OUTPUT
    - a list of all reduced forms equivalent to Q
    - a list of all nearly reduced forms equivalent to Q (ac < 0)
    - the automorph of Q (with trace > 2 and with the eigenspace (-b + sqrt(b^2 - 4ac), 2) associated to the eigenvalue > 1)
    - the automorph written as a word in S and T
    
    We compute these by performing the reduction algorithm to Q until we return to our original Q. 
    Along the way we keep track of the transformations we have applied to Q to find its automorph, 
    and also a representation of this automorph as a word in S and T. 
    We run in to all the reduced forms that are equivalent to Q along the way. 
    Each nearly reduced form lies between two reduced forms or its inversion does. 
    
    EXAMPLES:
    sage: Q = BinaryQF(1, 1, -1)
    sage: find_cycle(Q)
    (
    [x^2 + x*y - y^2, -x^2 + x*y + y^2],

    [-x^2 + x*y + y^2, x^2 - x*y - y^2, x^2 + x*y - y^2, -x^2 - x*y + y^2],

    [1 1]                     
    [1 2], ' S T^-1 S T^1 S S'
    )
    sage: (1 * principal_root(Q) + 2).norm()
    1
    '''
    if not Q.is_reduced():
        raise ValueError('%s is not reduced' % Q)
    if not Q.discriminant() > 0:
        raise ValueError('%s should have positive discriminant' % Q)
    
    S = matrix(ZZ, [[0, -1], [1, 0]])
    T = matrix(ZZ, [[1, 1], [0, 1]])
    
    assert Q.is_reduced()
    reduced_orbit = []
    nearly_reduced_orbit = []
    automorph = Matrix(ZZ, [[1, 0], [0, 1]])
    automorph_word_in_S_and_T = ''
    rounded_sqrt_disc = Q.discriminant().sqrt(prec=53).floor()
    
    original_Q = Q
    while True:
        # invert Q
        reduced_orbit.append(Q)
        [a, b], [c, d] = automorph
        Q = Q.matrix_action_right(S)
        automorph = automorph * S
        automorph_word_in_S_and_T += ' S'
    
        # translate Q to a reduced form
        
        (a, b, c) = Q
        n = ((-b + rounded_sqrt_disc)/(2*abs(a))).floor()
        for i in range(n):
            Q = Q.matrix_action_right(T^sign(a))

            
            # Each nearly reduced form either lies between two reduced forms, 
            # or its inversion does
            nearly_reduced_orbit.append(Q)
            nearly_reduced_orbit.append(Q.matrix_action_right(S)) 
        
        automorph = automorph * T^(sign(a)*n)
        automorph_word_in_S_and_T += ' T^%s' % (sign(a)*n)
    
        #assert Q.is_reduced()
        
        if (Q == original_Q): # we have completed the cycle
            
            if automorph.trace() < 0:
                # replace automorph to -automorph
                automorph = -automorph
                automorph_word_in_S_and_T += ' S S'
    
            #[a, b], [c, d] = automorph
            #assert c*principal_root(Q) + d > 1
            
            return(reduced_orbit, nearly_reduced_orbit, automorph, automorph_word_in_S_and_T)
            
                
def class_group_representatives(disc):
    '''
    Given a positive discriminant that is not a square,
    gives a set of representatives for the set of binary quadratic 
    forms of that discriminant modulo the action of SL2Z
    
    INPUT: 
    - `disc`: an integer > 0 not a square
    
    OUTPUT: 
    - A list of binary quadratic forms representing the set of binary quadratic 
    forms with discriminant `disc` modulo the action of SL2Z
    
    ALGORITHM: 
    The discriminant of Q = <a, b, c> is b^2 - 4ac. Each binary quadratic form 
    is equivalent to a reduced form (i.e. a form with ac < 0 and b > |a + c|)
    We loop over all values of b with 0 < b < sqrt(disc) and then the possibilities of a
    are the divisors of (disc - b^2)/4. We check if we have not seen an equivalent form before 
    and add Q = <a, b, (b^2 - disc)/4a> otherwise. 

    EXAMPLES: 
    sage: class_group_representatives(136)
    [5*x^2 + 4*x*y - 6*y^2,
     5*x^2 + 6*x*y - 5*y^2,
     2*x^2 + 8*x*y - 9*y^2,
     9*x^2 + 8*x*y - 2*y^2]

    sage: discriminants = [D for D in range(1, 500) if D % 4 in [0, 1] and not ZZ(D).is_square()]
    sage: from collections import Counter
    sage: Counter([len(class_group_representatives(D)) for D in discriminants])
    Counter({2: 108, 1: 55, 4: 53, 3: 4, 6: 4, 8: 2, 5: 1})
    '''
    if disc <= 0:
        raise ValueError('Algorithm not implemented for negative discriminants')
    if ZZ(disc).is_square(): 
        raise ValueError('Algorithm not implemented for square discriminants')
    if disc % 4 not in [0, 1]:
        return([])
    
    reduced_forms = []
    reduced_cycles_representatives = []
    for b in range(1, ceil(sqrt(disc))):
        if not b % 2 == disc % 2: 
            continue
        
        ac = (b^2 - disc)/4
        positive_divisors = divisors(ac)
        all_divisors = positive_divisors + [-k for k in positive_divisors]

        for a in divisors(ac):
            #positive a:
            c = ac/a
            Q = BinaryQF(a, b, c)
            #print(Q)
            if b <= (a + c).abs() or gcd([a, b, c]) != 1 or Q in reduced_forms:
                continue
            
            Qcycle = find_cycle(Q)[0]
            reduced_forms += Qcycle
            reduced_cycles_representatives.append(Q)
            
    return(reduced_cycles_representatives)  

def compute_xi(nearly_reduced_orbit):
    '''
    Computes the constant xi as described in Lemma 2.1 from 
    'Singular moduli for real quadratic fields: a rigid analytic approach' by Darmon and Vonk
    
    INPUT: 
    a list of all nearly reduced forms equivalent to some binary quadratic form
    '''
    xi = 1
    for Q in nearly_reduced_orbit:
        a, b, c = Q
        if a > 0: #this means root_Q = (-b + sqrt(b^2-4*a*c))/2*a > 0
            root_Q = principal_root(Q)
            assert root_Q > 0
            xi *= root_Q
    return(xi)

def compute_naive_knopp(nearly_reduced_orbit):
    '''
    Computes the value bar{j^circ_tau} from Lemma 2.1 from 
    'Singular moduli for real quadratic fields: a rigid analytic approach' by Darmon and Vonk
    '''
    K = principal_root(nearly_reduced_orbit[0]).parent()
    sqrtdisc = K.gen()
    Kz.<z> = PolynomialRing(K)
    naive_knopp = Kz(1)
    for Q in nearly_reduced_orbit:
        a, b, c = Q
        root_Q = (-b + sqrtdisc)/(2*a)
        
        naive_knopp *= (z-root_Q)^(sign(a))
        
    return(naive_knopp)

def compute_Knopp_in_S_and_T(Q):
    '''
    Computes the values of Kn_Q(S) and Kn_Q(T) using Lemma 2.2 of [DV]
    
    INPUT: 
    - an indefinite binary quadratic form Q
    '''


    #print(disc)
            
    Q = Q.reduced_form()
    reduced_orbit, nearly_reduced_orbit, automorph, automorph_word_in_S_and_T = find_cycle(Q)
    xi = compute_xi(nearly_reduced_orbit)
    tau_Q = principal_root(Q)
    [a, b], [c, d] = automorph
    unit = (c*tau_Q + d)^-1

    naive_knopp = compute_naive_knopp(nearly_reduced_orbit)
    Kz = naive_knopp.parent()
    
    KnoppS = naive_knopp / xi
    KnoppT = Kz(unit) 
    
    return(KnoppS, KnoppT)

def left_slash_action(matrix, rational_function, weight=0):
    '''
    Given a matrix gamma in SL2Z and a rational function f(z), 
    computes gamma * f(z)
    
    INPUT: 
     - a matrix gamma in SL2Z
     - a rational function f
    (- the weight of the action)
    '''
    #print(rational_function.parent())
    z = rational_function.parent().gen()
    [a, b], [c, d] = matrix^-1
    return((c*z+d)^-weight * rational_function((a*z + b)/(c*z + d)))


def evaluate_Knopp_in_matrix(KnoppS, KnoppT, matrix_as_word):
    '''
    Computes the value of the Knopp cocycle in a matrix using the cocycle relation 
    and its values in the generators S, T of SL2Z. 
    
    INPUT:
    - 
    '''
    Kz = KnoppS.parent()
    
    cumulative_matrix = matrix([[1, 0], [0, 1]])
    Knopp = Kz(1)
    for SorTn in matrix_as_word: #run through the S and T^n from left to right
        # Repeatedly use the equality 
        # Kn(alpha_1 ... alpha_n beta) = Kn(alpha_1 ... alpha_n) times ((alpha_1 ... alpha_n) star Kn(beta))
        if SorTn == 'S': 
            S = matrix([[0, -1], [1, 0]])
            Knopp *= left_slash_action(cumulative_matrix, KnoppS)
            cumulative_matrix = cumulative_matrix * S
        else: #matrix is of the form 'T^n'
            n = ZZ(SorTn[2:])
            Tn = matrix([[1, n], [0, 1]])
            cumulative_matrix = cumulative_matrix * Tn
            Knopp *= KnoppT^n
        
        #print(cumulative_matrix)
        #print(Knopp)
    return(Knopp)

def write_matrix_as_word(gamma):
    '''
    Given a matrix in SL2Z, write it as a word in S and T (represented as a string)

    Examples: 
    sage: U = matrix([[1, -1], [1, 0]])
    sage: write_matrix_as_word(U)
    'T^1 S '
    '''
    QI.<I> = NumberField(x^2+1)
    [a, b], [c, d] = gamma^-1
    tau = (a*2*I + b)*(c*2*I + d)^-1 # = gamma^-1 2i
    word = ''
    
    reconstructed_gamma = matrix([[1, 0], [0, 1]])
    S = matrix([[0, -1], [1, 0]])
    T = matrix([[1, 1], [0, 1]])
    # applying the reduction algorithm to tau to move it back to the fundamental domain
    
    while not (tau.norm() >= 1 and tau[0].abs() <= 0.5):
        if tau.norm() < 1:
            # inverting
            tau = -tau^-1
            word = 'S ' + word
            reconstructed_gamma = S*reconstructed_gamma
            
        # translating    
        n = - round(tau[0])
        tau = tau + n
        if n != 0:
            word = ('T^%s ' % n) + word
            reconstructed_gamma = T^n*reconstructed_gamma
    
    # we now have the right representation up to sign
    if reconstructed_gamma == -gamma:
        word = 'S S ' + word
    else:
        assert reconstructed_gamma == gamma
    
    return(word)


def Knopp_cocycle(Q, gamma):
    '''
    Computes the value of the Knopp cocycle Kn_Q in the matrix gamma by first computing 
    the value of Kn_Q in S and T and then using the cocyle relation
    Examples: 
    sage: Q = BinaryQF(1, 1, -1)
    sage: S = matrix([[0, -1], [1, 0]])
    sage: Knopp_cocycle(Q, S)
    (z^2 - sqrt5*z + 1)/(z^2 + sqrt5*z + 1)
    sage: Knopp_cocycle(Q, 'S')
    (z^2 - sqrt5*z + 1)/(z^2 + sqrt5*z + 1)
    sage: Knopp_cocycle(Q, ['S'])
    (z^2 - sqrt5*z + 1)/(z^2 + sqrt5*z + 1)

    sage: U = matrix([[1, -1], [1, 0]])
    sage: Knopp_cocycle(Q, U)
    ((-1/2*sqrt5 + 3/2)*z^2 + (-1/2*sqrt5 - 1/2)*z + 1/2*sqrt5 + 1/2)/(z^2 + (sqrt5 - 2)*z - sqrt5 + 2)
    sage: Knopp_cocycle(Q, 'T^1 S')
    ((-1/2*sqrt5 + 3/2)*z^2 + (-1/2*sqrt5 - 1/2)*z + 1/2*sqrt5 + 1/2)/(z^2 + (sqrt5 - 2)*z - sqrt5 + 2)
    sage: Knopp_cocycle(Q, ['T^1', 'S'])
    ((-1/2*sqrt5 + 3/2)*z^2 + (-1/2*sqrt5 - 1/2)*z + 1/2*sqrt5 + 1/2)/(z^2 + (sqrt5 - 2)*z - sqrt5 + 2)
    '''
    Q = Q.reduced_form()
    KnQS, KnQT = compute_Knopp_in_S_and_T(Q)
    
    #we make sure gamma is in the correct form:
    if type(gamma) == str:
        gamma = gamma.split()
        
    if  type(gamma) != list:
        # gamma is a matrix and we need to write it as a word in S and T
        gamma = write_matrix_as_word(gamma).split()
        
    return(evaluate_Knopp_in_matrix(KnQS, KnQT, gamma))
               

    
    
def Theta(Q1, Q2):
    '''
    Computes Theta(Q1, Q2) as defined in my thesis. It is equal to Kn_{Q1}[Q2] = Kn_{Q1}(gamma_Q2)(root_Q2)
    
    INPUT: 
     - two binary quadratic forms with non-square positive discriminants
    
    EXAMPLES: 
    sage: Q1 = BinaryQF(1, 1, -1)
    sage: Q2 = BinaryQF(1, 2, -1)
    sage: Theta(Q1, Q2)
    1

    sage: Q1 = BinaryQF(1, 1, -1)
    sage: Q2 = BinaryQF(2, 2, -1)
    sage: Theta(Q1, Q2).minpoly()
    x^2 + 147/11*x + 1

    sage: Q1 = BinaryQF(4, 6, -7)
    sage: Q2 = BinaryQF(7, 6, -10)
    sage: f = Theta(Q1, Q2).minpoly()
    sage: f *= lcm([ai.denominator() for ai in f.coefficients()])
    sage: print(f)
    1932404095170907030264359057729397827008726868759052041951451351988561892462708697*x^4 - 4306435258386914218036226884073702969386340275372644597995378230700574931870323193172025188*x^3 - 14335270990687861756254357363169891601512209118402872071205989182796448348557888969017462382942327018*x^2 + 1673185694775894168010946749258487874368640510237139298991336652824983124019268555005894812*x + 62611282959971165236114513553945184977289328158699272876446643264567685445748697
    sage: f[0].factor()
    3^3 * 7^2 * 17^2 * 19^2 * 29^2 * 73^3 * 101 * 107 * 139 * 181^2 * 269 * 271 * 379^2 * 419^2 * 433 * 761 * 1163 * 1381 * 1489 * 1601 * 3617 * 3889 * 8443 * 9091 * 11251
    '''
    Q1 = Q1.reduced_form()
    Q2 = Q2.reduced_form()

    
    automorph_of_Q2_as_word_in_S_and_T = find_cycle(Q2)[3].split()
    KnQ1gammaQ2 = Knopp_cocycle(Q1, automorph_of_Q2_as_word_in_S_and_T)
    disc1 = Q1.discriminant()
    disc2 = Q2.discriminant()
    generator_name_K1 = 'sqrt' + str(disc1)
    generator_name_K2 = 'sqrt' + str(disc2)
    K1 = NumberField(x^2 - disc1, generator_name_K1, embedding=RR(sqrt(disc1)))
    
    K2 = NumberField(x^2 - disc2, generator_name_K2, embedding=RR(sqrt(disc2)))
    L = K1.composite_fields(K2, 'a')[0]
    sqrtdisc1 = L(K1.gen()) 
    sqrtdisc2 = L(K2.gen())
    
        # this compositum has generator a, which is equal to sqrt(discG) + n*sqrt(discF)
        # for some integer n
    a, b, c = Q2
    root_Q2 = (-b + sqrtdisc2)/(2*a)
        
    return(KnQ1gammaQ2(root_Q2))
