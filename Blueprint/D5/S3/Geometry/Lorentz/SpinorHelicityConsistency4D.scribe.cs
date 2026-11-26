using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class SpinorHelicityConsistency4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.";
    private static readonly Formula K = F.Id("K"), I = F.Id("I"), U = F.Id("u"), V = F.Id("v"),
        W = F.Id("w"), Z = F.Id("z"), A = F.Id("A"), P = F.Id("P"),
        L = F.Id("l"), R = F.Id("r"), X = F.Id("X"), Ff = F.Id("f"),
        G = F.Id("g"), B = F.Id("b"), C = F.Id("c"), E = F.Id("e"), Dd = F.Id("d"),
        a = F.Id("a"), s = F.Id("s"), t = F.Id("t"), u = F.Id("u"),
        Cs = Sub(C, "s"), Ct = Sub(C, "t"), Cu = Sub(C, "u"),
        Kg = Sub(F.Id("k"), "g"), Ka = Sub(F.Id("k"), "a");
    private static Formula Spinor(Formula k) => Pow(k, D(2));
    private static Formula Mat(Formula i, Formula k) => Call("Mat", i, i, k);
    private static Formula MvPoly => Call("MvPolynomial", Call("Fin", D(2)), K);
    private static Formula Species => Arrow(I, Arrow(I, Arrow(I, K)));
    private static Formula Br(Formula x, Formula y) => Call("angle", x, y);
    private static Formula Bi(Formula x, Formula y) => Call("bispinor", x, y);
    private static Formula S(int i, int j) => Call("mandelstam", L, R, Num(i), Num(j));
    private static Formula Hf => Call("H", L, R);
    private static Formula Al(int i, int j) => Br(At(L, i), At(L, j));
    private static Formula PTdenOther => Mul(Al(0, 1), Al(1, 3), Al(3, 2), Al(2, 0));
    private static Formula PTden => Mul(Al(0, 1), Al(1, 2), Al(2, 3), Al(3, 0));
    private static Formula Conservation4 => EqF(SumF("i", Call("Fin", D(4)),
        Bi(At(L, F.Id("i")), At(R, F.Id("i")))), D(0));
    private static Formula Eval(string channel) => Call(channel, P);
    private static Formula Const(Formula x) => Call("C", x);
    private static Formula Restrict(Formula x, Formula y, Formula z) =>
        And(EqF(Eval("evalS"), x), EqF(Eval("evalT"), y), EqF(Eval("evalU"), z));
    private static Formula LowSpin(Formula x, Formula y, Formula z, Formula result) =>
        Field(AllVars(K, [Cs, Ct, Cu], Rel(Ex("P", MvPoly, Restrict(x, y, z)), Iff, result)));
    private static Formula Tensor(Formula f, Formula i, Formula j, Formula k) =>
        new Formula.Apply(f, [i, j, k]);
    private static Formula M(Formula g, Formula i) => Call("M", g, i);
    private static Formula Factor(Formula f, Formula i, Formula j, Formula k, Formula l) =>
        SumF("e", I, Mul(Tensor(f, i, j, E), Tensor(f, k, l, E)));
    private static Formula Symmetry(Formula f, bool antisym) =>
        AllVars(I, [a, B, C], And(
            EqF(Tensor(f, a, B, C), antisym ? Negative(Tensor(f, B, a, C)) : Tensor(f, B, a, C)),
            EqF(Tensor(f, a, B, C), antisym ? Negative(Tensor(f, a, C, B)) : Tensor(f, a, C, B))));
    private static Formula Residues(Formula g) => AllVars(I, [a, B, C, Dd], And(
        EqF(Factor(g, a, B, C, Dd), Factor(g, a, Dd, B, C)),
        EqF(Factor(g, a, Dd, B, C), Factor(g, a, C, Dd, B))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spinor brackets and four-point consistency of polynomial channel restrictions.",
        H("Four-dimensional spinor helicity and four-point consistency"),
        Blocks(
            Paragraph(Text("Let K be a field. Spinors are two-component vectors. Both chiralities use the alternating bracket angle(u,v) = u(0)v(1) - u(1)v(0). The bispinor is the outer product l rᵀ. For four particles numbered 0 through 3, mandelstam(l,r,i,j) is the product of the two brackets of particles i and j. The prefactor H(l,r) is the square of angle(l(0),l(2)) times the square of angle(r(1),r(3)).")),
            Node("bracket-antisymmetry", "angle_antisymm", "Bracket antisymmetry",
                "Exchange the two spinors in the alternating determinant.",
                Field(AllVars(Spinor(K), [U, V], EqF(Br(U, V), Negative(Br(V, U)))))),
            Node("bracket-self", "angle_self", "Vanishing on repeated spinors",
                "The two products in the determinant cancel.",
                Field(AllVars(Spinor(K), [U], EqF(Br(U, U), D(0))))),
            Node("bracket-covariance", "angle_det_covariance", "Determinant covariance",
                "Multiplication by a two-by-two matrix scales the bracket by its determinant. The bracket is invariant when this determinant is one.",
                Field(AllVars(Mat(Call("Fin", D(2)), K), [A], AllVars(Spinor(K), [U, V],
                    EqF(Br(Mul(A, U), Mul(A, V)), Mul(Call("det", A), Br(U, V))))))),
            Node("schouten", "schouten_identity", "Schouten identity",
                "Expansion of the three products of alternating determinants cancels all monomials.",
                Field(AllVars(Spinor(K), [U, V, W, Z], EqF(Add(
                    Mul(Br(U, V), Br(W, Z)), Mul(Br(U, W), Br(Z, V)), Mul(Br(U, Z), Br(V, W))), D(0))))),
            Node("spinor-frame", "spinor_frame_transport", "Determinant-one frame transport",
                "A nonzero bracket determines a basis. Schouten expresses the third spinor in that basis using its two brackets. Equality of the three brackets constructs a determinant-one matrix transporting the two frames and the third spinor.",
                FrameTransport()),
            Node("null-bispinor", "bispinor_det", "Null bispinor",
                "The determinant of the outer product vanishes.",
                Field(AllVars(Spinor(K), [L, R], EqF(Call("det", Bi(L, R)), D(0))))),
            Node("mandelstam-determinant", "mandelstam_det", "Mandelstam determinant",
                "In the determinant of a sum of two outer products only the mixed terms survive.",
                Field(AllVars(Spinor(K), [Sub(L, 1), Sub(R, 1), Sub(L, 2), Sub(R, 2)],
                    EqF(Call("det", Add(Bi(Sub(L, 1), Sub(R, 1)), Bi(Sub(L, 2), Sub(R, 2)))),
                        Mul(Br(Sub(L, 1), Sub(L, 2)), Br(Sub(R, 1), Sub(R, 2))))))),
            Node("null-factorization", "null_bispinor_factorization_iff", "Null bispinor factorization",
                "A matrix with vanishing determinant and a nonzero entry has proportional rows and columns, giving an outer-product factorization by division at that entry. The zero matrix also factors.",
                Field(AllVars(Mat(Call("Fin", D(2)), K), [A], Rel(EqF(Call("det", A), D(0)), Iff,
                    Ex("l", Spinor(K), Ex("r", Spinor(K), EqF(A, Bi(L, R)))))))),
            Node("three-point-dichotomy", "three_point_kinematics_dichotomy", "Three-point complex kinematics",
                "If a left bracket is nonzero, its spinors are independent, and momentum conservation expresses their right spinors as multiples of the third. Hence all right brackets vanish. The complementary case has all left brackets zero.",
                ThreePoint(false)),
            Node("three-point-real", "three_point_real_brackets_vanish", "Conjugate spinors",
                "For right spinors equal to the conjugates of the left spinors, the right brackets are conjugates of the left brackets. Consequently both sets vanish.",
                ThreePoint(true)),
            Node("three-point-scaled-conjugate", "three_point_scaled_conjugate_brackets_vanish", "Scaled conjugate spinors",
                "Nonzero scalar multiples of the conjugate spinors multiply each conjugate bracket by a nonzero factor. Both bracket families vanish under momentum conservation. Real signs allow both time orientations.",
                ScaledConjugate()),
            Node("little-group", "three_point_little_group_exponents_unique", "Unique three-point exponents",
                "Adding two scaling equations and subtracting the third isolates twice one exponent. This determines each integer exponent uniquely.",
                LittleGroup()),
            Node("parke-taylor-polynomial", "four_point_parke_taylor_polynomial", "Parke–Taylor polynomial identity",
                "Contract momentum conservation on the left with spinor 2 and on the right with spinors 1 and 3. Multiplying the resulting two identities and using antisymmetry gives the signed, denominator-cleared relation even at zero brackets.",
                FourPoint(Rel(Conservation4, Implies, EqF(Mul(Hf, PTden),
                    Negative(Mul(Pow(Al(0, 2), D(4)), S(0, 1), S(0, 3))))))),
            Node("parke-taylor-ratio", "four_point_parke_taylor_mandelstam_identity", "Parke–Taylor ratio",
                "Where the two denominators are nonzero, division of the polynomial identity gives the ratio. The minus sign follows from the oriented last bracket and the determinant convention.",
                FourPoint(Rel(And(Conservation4, NeF(Mul(S(0, 1), S(0, 3)), D(0)), NeF(PTden, D(0))),
                    Implies, EqF(Div(Hf, Mul(S(0, 1), S(0, 3))),
                        Negative(Div(Pow(Al(0, 2), D(4)), PTden)))))),
            Node("klt", "four_point_klt_identity", "Four-point KLT product",
                "The rational product has the KLT channel denominators and a squared prefactor. The identity also holds with total field division at zero denominators.",
                Klt()),
            Node("klt-parke-taylor", "four_point_klt_parke_taylor", "KLT product of ordered Parke–Taylor ratios",
                "Pair momentum conservation equates the complementary Mandelstam determinants. The second ordering has the signed ratio with denominator s12 s13. The two minus signs cancel in the KLT product.",
                KltParkeTaylor()),
            Paragraph(Text("For a polynomial P in K[s,t], write evalS(P) = P(0,X), evalT(P) = P(X,0), and evalU(P) = P(X,-X), each in K[X]. The map C embeds a scalar as a constant polynomial. The constant terms of the three restrictions agree. The linear coefficient on the third line equals the linear coefficient on the second minus that on the first. These relations hold for arbitrary polynomial degree. The following compatibility conditions concern tree numerator polynomials with the stated channel restrictions for their factorization residues.")),
            Node("spin-one", "spin_one_four_point_consistency_iff", "Spin-one channel consistency",
                "Necessity follows by comparing the linear coefficients. Sufficiency is realized by the polynomial -c_t s + c_s t.",
                LowSpin(Mul(Const(Cs), X), Mul(Const(Negative(Ct)), X), Mul(Const(Cu), X),
                    EqF(Add(Cs, Ct, Cu), D(0)))),
            Node("spin-two", "spin_two_four_point_consistency_iff", "Spin-two channel consistency",
                "Equality of constant terms forces all three residues to agree. A constant polynomial realizes every such triple.",
                LowSpin(Const(Cs), Const(Ct), Const(Cu), And(EqF(Cs, Ct), EqF(Ct, Cu)))),
            Node("equivalence-principle", "equivalence_principle_from_consistency", "Universal nonzero coupling",
                "The spin-two condition on the single-graviton and species couplings is k_g k_a = k_a². A field has no zero divisors, so each coupled species has the graviton self-coupling.",
                Field(AllVars(K, [Kg, Ka], Rel(Ex("P", MvPoly,
                    Restrict(Const(Mul(Kg, Ka)), Const(Pow(Ka, D(2))), Const(Pow(Ka, D(2))))),
                    Iff, Rel(EqF(Ka, D(0)), Lor, EqF(Ka, Kg)))))),
            Node("higher-spin", "higher_spin_four_point_exclusion_iff", "Higher-spin channel exclusion",
                "For spin at least three, the positive power of X annihilates the constant coefficient on each line. All three prescribed constants must therefore vanish. The zero polynomial suffices when they vanish.",
                HigherSpin()),
            Paragraph(Text("Let I be a finite type of species. The coupling f is totally antisymmetric under adjacent exchanges for spin one. For spin two, a totally symmetric cubic coupling g determines the matrix M(g,a) with entry (b,c) equal to g(a,b,c). Its species product Q(g,x,y) is the sum of x(a) M(g,a)y over a.")),
            Node("jacobi", "spin_one_jacobi_from_consistency", "Jacobi identity from color residues",
                "The spin-one compatibility condition forces the sum of the three contracted color factors to vanish. Total antisymmetry converts them to the ordinary Jacobi contraction.",
                Jacobi()),
            Node("graviton-matrices", "multi_graviton_commutativity_and_decoupling", "Commutativity and associativity",
                "Each matrix product entry is one of the three residue contractions. Total symmetry identifies the reversed product with the second contraction and the weighted sum of matrices with the first.",
                SpeciesField(AllVars(Species, [G], Rel(Symmetry(G, false), Implies,
                    Rel(Residues(G), Iff, AllVars(I, [a, B], And(
                        EqF(Mul(M(G, a), M(G, B)), Mul(M(G, B), M(G, a))),
                        EqF(Mul(M(G, a), M(G, B)), SumF("e", I, Mul(Tensor(G, a, B, E), M(G, E))))))))))),
            Node("graviton-cross", "graviton_cross_product_zero", "Independent joint eigenvectors decouple",
                "Symmetry makes the species product commutative. For two common eigenvectors it is simultaneously a scalar multiple of each. Linear independence makes both scalars vanish.",
                CrossProduct()),
            Node("graviton-spectrum", "multi_graviton_joint_eigenspaces", "Joint eigenspaces span the real species space",
                "The residue equations make the real symmetric coupling matrices commute. The joint eigenspaces of the corresponding Euclidean linear operators exhaust the species space. Common eigenvectors can be chosen as a basis, and the preceding vanishing identity eliminates mixed products of distinct basis vectors.",
                Spectrum()),
            Node("graviton-basis", "multi_graviton_decoupled_basis", "A decoupled basis of species",
                "The set of joint eigenvectors spans the Euclidean species space. A basis extracted from this spanning set transports to species coordinate space. Products between distinct basis vectors vanish by their linear independence.",
                DecoupledBasis()),
            Node("graviton-counterexample", "two_graviton_noncommuting_example", "A noncommuting symmetric two-species coupling",
                "Take g(a,b,c) equal to one when exactly one of the three indices is 1, and zero otherwise. The (0,1) entries of the two ordered matrix products differ.",
                TwoSpecies())),
        []));

    private static Formula FrameTransport()
    {
        Formula x = F.Id("x"), y = F.Id("y");
        return Field(AllVars(Spinor(K), [U, V, W, x, y, Z], Rel(And(
            NeF(Br(U, V), D(0)), EqF(Br(U, V), Br(x, y)), EqF(Br(U, W), Br(x, Z)),
            EqF(Br(V, W), Br(y, Z))), Implies, Ex("A", Mat(Call("Fin", D(2)), K), And(
            EqF(Call("det", A), D(1)), EqF(Mul(A, U), x), EqF(Mul(A, V), y), EqF(Mul(A, W), Z))))));
    }

    private static Formula ScaledConjugate()
    {
        Formula complex = NumberField("C"), l1 = Sub(L, 1), l2 = Sub(L, 2), l3 = Sub(L, 3);
        Formula r1 = Mul(a, Conj(l1)), r2 = Mul(B, Conj(l2)), r3 = Mul(C, Conj(l3));
        return AllVars(Spinor(complex), [l1, l2, l3], AllVars(complex, [a, B, C], Rel(
            And(NeF(a, D(0)), NeF(B, D(0)), NeF(C, D(0)),
                EqF(Add(Bi(l1, r1), Bi(l2, r2), Bi(l3, r3)), D(0))), Implies,
            And(ZeroBrackets(l1, l2, l3), ZeroBrackets(r1, r2, r3)))));
    }

    private static Formula KltParkeTaylor()
    {
        Formula numerator = Pow(Al(0, 2), D(4));
        return FourPoint(Rel(And(Conservation4, NeF(Mul(S(0, 1), S(0, 3)), D(0)),
            NeF(Mul(S(0, 1), S(0, 2)), D(0)), NeF(PTden, D(0)), NeF(PTdenOther, D(0))),
            Implies, EqF(Mul(Negative(S(0, 1)), Div(numerator, PTden), Div(numerator, PTdenOther)),
                Div(Negative(Pow(Hf, D(2))), Mul(S(0, 1), S(0, 3), S(0, 2))))));
    }

    private static Formula DecoupledBasis()
    {
        Formula real = NumberField("R"), vec = Arrow(I, real), basis = F.Id("B");
        Formula i = F.Id("i"), j = F.Id("j"), chi = F.Id("chi");
        Formula bi = At(basis, i), bj = At(basis, j);
        Formula eigen = AllVars(I, [i], Ex("chi", vec, AllVars(I, [a],
            EqF(Mul(M(G, a), bi), Mul(At(chi, a), bi)))));
        Formula cross = AllVars(I, [i, j], Rel(NeF(i, j), Implies, EqF(Call("Q", G, bi, bj), D(0))));
        return All("I", Operator("Type"), Seq(Class("Fintype", I), Sp,
            AllVars(Arrow(I, Arrow(I, vec)), [G], Rel(And(Symmetry(G, false), Residues(G)),
                Implies, Ex("B", Call("Basis", I, real, vec), And(eigen, cross))))));
    }

    private static Formula ThreePoint(bool real)
    {
        Formula l1 = Sub(L, 1), l2 = Sub(L, 2), l3 = Sub(L, 3);
        Formula r1 = real ? Conj(l1) : Sub(R, 1);
        Formula r2 = real ? Conj(l2) : Sub(R, 2);
        Formula r3 = real ? Conj(l3) : Sub(R, 3);
        Formula left = ZeroBrackets(l1, l2, l3), right = ZeroBrackets(r1, r2, r3);
        Formula body = Rel(EqF(Add(Bi(l1, r1), Bi(l2, r2), Bi(l3, r3)), D(0)), Implies,
            real ? And(left, right) : Rel(left, Lor, right));
        return real ? AllVars(Spinor(NumberField("C")), [l1, l2, l3], body)
            : Field(AllVars(Spinor(K), [l1, l2, l3, r1, r2, r3], body));
    }

    private static Formula ZeroBrackets(Formula x, Formula y, Formula z) =>
        And(EqF(Br(x, y), D(0)), EqF(Br(y, z), D(0)), EqF(Br(z, x), D(0)));

    private static Formula LittleGroup()
    {
        Formula h = F.Id("h"), d = F.Id("d");
        Formula h1 = Sub(h, 1), h2 = Sub(h, 2), h3 = Sub(h, 3);
        Formula d1 = Sub(d, 1), d2 = Sub(d, 2), d3 = Sub(d, 3);
        return AllVars(NumberField("Z"), [h1, h2, h3, d1, d2, d3], Rel(
            And(EqF(Add(d2, d3), Mul(Negative(D(2)), h1)),
                EqF(Add(d3, d1), Mul(Negative(D(2)), h2)), EqF(Add(d1, d2), Mul(Negative(D(2)), h3))),
            Iff, And(EqF(d1, Subtract(Subtract(h1, h2), h3)), EqF(d2, Subtract(Subtract(h2, h3), h1)),
                EqF(d3, Subtract(Subtract(h3, h1), h2)))));
    }

    private static Formula FourPoint(Formula body) => Field(AllVars(Arrow(Call("Fin", D(4)), Spinor(K)), [L, R], body));
    private static Formula Klt()
    {
        Formula k = F.Id("k");
        return Field(AllVars(K, [k, s, t, u], EqF(
            Mul(Negative(s), Div(k, Mul(s, t)), Div(k, Mul(s, u))),
            Div(Negative(Pow(k, D(2))), Mul(s, t, u)))));
    }

    private static Formula HigherSpin()
    {
        Formula power = Pow(X, Subtract(s, D(2)));
        return Field(AllVars(NumberField("N"), [s], AllVars(K, [Cs, Ct, Cu],
            Rel(Rel(D(3), Leq, s), Implies, Rel(Ex("P", MvPoly, And(
                EqF(Mul(power, Eval("evalS")), Const(Cs)),
                EqF(Mul(power, Eval("evalT")), Const(Mul(Pow(Negative(D(1)), s), Ct))),
                EqF(Mul(power, Eval("evalU")), Const(Cu)))), Iff,
                And(EqF(Cs, D(0)), EqF(Ct, D(0)), EqF(Cu, D(0))))))));
    }

    private static Formula Jacobi()
    {
        Formula sum = SumF("e", I, Add(
            Mul(Tensor(Ff, a, B, E), Tensor(Ff, E, C, Dd)),
            Mul(Tensor(Ff, B, C, E), Tensor(Ff, E, a, Dd)),
            Mul(Tensor(Ff, C, a, E), Tensor(Ff, E, B, Dd))));
        return SpeciesField(AllVars(Species, [Ff], Rel(Symmetry(Ff, true), Implies,
            AllVars(I, [a, B, C, Dd], Rel(Ex("P", MvPoly, Restrict(
                Mul(Const(Factor(Ff, a, B, C, Dd)), X),
                Mul(Const(Negative(Factor(Ff, a, Dd, B, C))), X),
                Mul(Const(Factor(Ff, a, C, Dd, B)), X))),
                Implies, EqF(sum, D(0)))))));
    }

    private static Formula CrossProduct()
    {
        Formula x = F.Id("x"), y = F.Id("y"), chi = F.Id("chi"), psi = F.Id("psi");
        Formula eigen = AllVars(I, [a], And(EqF(Mul(M(G, a), x), Mul(new Formula.Apply(chi, [a]), x)),
            EqF(Mul(M(G, a), y), Mul(new Formula.Apply(psi, [a]), y))));
        return SpeciesField(AllVars(Species, [G], Rel(Symmetry(G, false), Implies,
            AllVars(Arrow(I, K), [x, y, chi, psi], Rel(And(eigen, Call("LinearIndependent", K, Seq(OpenBracket, x, Comma, y, CloseBracket))),
                Implies, EqF(Call("Q", G, x, y), D(0)))))));
    }

    private static Formula Spectrum()
    {
        Formula real = NumberField("R");
        Formula chi = F.Id("chi");
        Formula spec = EqF(Seq(Operator("sup"), Underscore, Grp(Seq(chi, Colon, Arrow(I, real))), Sp,
            Operator("inf"), Underscore, Grp(Seq(a, Colon, I)), Sp,
            Call("eigenspace", Call("toEuclideanLin", M(G, a)), new Formula.Apply(chi, [a]))),
            Operator("top"));
        return All("I", Operator("Type"), Seq(Class("Fintype", I), Sp, Class("DecidableEq", I), Sp,
            AllVars(Arrow(I, Arrow(I, Arrow(I, real))), [G],
                Rel(And(Symmetry(G, false), Residues(G)), Implies, spec))));
    }

    private static Formula TwoSpecies()
    {
        Formula real = NumberField("R"), fin = Call("Fin", D(2));
        return Ex("g", Arrow(fin, Arrow(fin, Arrow(fin, real))), And(
            AllVars(fin, [a, B, C], And(EqF(Tensor(G, a, B, C), Tensor(G, B, a, C)),
                EqF(Tensor(G, a, B, C), Tensor(G, a, C, B)))),
            NeF(Mul(M(G, D(0)), M(G, D(1))), Mul(M(G, D(1)), M(G, D(0))))));
    }

    private static DocumentBlock Node(string id, string name, string title, string prose, Formula formula) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Field(Formula body) =>
        All("K", Operator("Type"), Seq(Class("Field", K), Sp, body));
    private static Formula SpeciesField(Formula body) =>
        Field(All("I", Operator("Type"), Seq(Class("Fintype", I), Sp, body)));
    private static Formula Class(string name, Formula arg) => Seq(OpenBracket, Call(name, arg), CloseBracket);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Parens(new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body));
    private static Formula AllVars(Formula type, Formula[] vars, Formula body)
    {
        var parts = new List<Formula> { Forall, Sp };
        foreach (Formula v in vars)
            parts.AddRange([v, Sp]);
        parts.AddRange([Colon, Sp, type, Comma, Sp, body]);
        return Parens(Seq([.. parts]));
    }
    private static Formula Operator(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Operator(name), [..args]);
    private static Formula At(Formula f, int i) => At(f, Num(i));
    private static Formula At(Formula f, Formula i) => new Formula.Apply(f, [i]);
    private static Formula Num(int i) => D((byte)i);
    private static Formula Sub(Formula v, int i) => Seq(v, Underscore, Grp(Num(i)));
    private static Formula Sub(Formula v, string i) => Seq(v, Underscore, Grp(F.Id(i)));
    private static Formula NumberField(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula Conj(Formula x) => Seq(Overline, Grp(x));
    private static Formula Pow(Formula x, Formula d) => Seq(Parens(x), Caret, Grp(d));
    private static Formula Div(Formula n, Formula d) => Seq(Frac, Grp(n), Grp(d));
    private static Formula Arrow(Formula x, Formula y) => Rel(x, To, y);
    private static Formula Negative(Formula x) => Parens(Seq(Minus, Sp, x));
    private static Formula Subtract(Formula x, Formula y) => Rel(x, Minus, y);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Parens(Seq(left, Sp, relation, Sp, right));
    private static Formula EqF(Formula x, Formula y) => Rel(x, Eq, y);
    private static Formula NeF(Formula x, Formula y) => Rel(x, Neq, y);
    private static Formula Parens(Formula formula) => Seq(Open, formula, Close);
    private static Formula And(params Formula[] terms) => Join(Land, terms);
    private static Formula Add(params Formula[] terms) => Join(Plus, terms);
    private static Formula Mul(params Formula[] terms) => Join(Cdot, terms);
    private static Formula Join(Formula relation, Formula[] terms)
    {
        var parts = new List<Formula> { terms[0] };
        foreach (Formula term in terms[1..])
            parts.AddRange([Sp, relation, Sp, term]);
        return Parens(Seq([..parts]));
    }
    private static Formula SumF(string index, Formula type, Formula term) =>
        Seq(Sum, Underscore, Grp(Seq(F.Id(index), Colon, type)), Sp, Parens(term));
}
