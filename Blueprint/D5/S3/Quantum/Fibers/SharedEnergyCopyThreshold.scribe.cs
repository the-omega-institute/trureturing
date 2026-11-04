using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class SharedEnergyCopyThresholdDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse positive density matrices in the fixed three-level energy basis have "
            + "a phase-sensitive relation of degree twice the upper energy minus one.",
        H("Sparse Shared Energy Relations"), Blocks(
            Def("matrix", "sparseMatrix", "Literal sparse Hermitian matrices",
                "The diagonal entries are one third. The entries between the first and "
                    + "second basis vectors vanish. Entries (2,0) and (0,2) are u divided "
                    + "by twelve and its conjugate; entries (2,1) and (1,2) are one twelfth. "
                    + "Both edge moduli are one twelfth when u has unit modulus."),
            Thm("spectrum", "sparse_density_spectrum", "Positive density spectrum", Spectrum(),
                "For every complex phase of unit modulus, the literal matrix is positive "
                    + "definite and has trace one. Its spectrum is exactly the stated three "
                    + "real numbers. Factoring the determinant of the shifted matrix gives "
                    + "the spectrum; its smallest element is strictly positive."),
            Def("state", "sparseState", "Native density states",
                "The literal matrix enters the native positive trace-one DensityState "
                    + "subtype through its star algebra equivalence. Positivity and trace "
                    + "normalization are proved, rather than assumed as independent coordinates."),
            Def("phase", "phase", "The resonant phase",
                "For a natural number m the phase is the circle exponential at pi divided "
                    + "by m minus one. When m is at least two, its power m minus one is "
                    + "minus one. This includes the coincident numerical gaps at m equal to two."),
            Def("first", "rho", "First sparse density state",
                "The first native state uses phase one and has both nonzero coherences "
                    + "equal to one twelfth."),
            Def("second", "sigma", "Second sparse density state",
                "The second native state has the same diagonal and zero entries and "
                    + "uses the resonant phase on the edge between the first and third levels."),
            Def("relation", "starMonomial", "The phase-sensitive supported monomial",
                "The monomial is the entry from level two to level one to the power m, "
                    + "times the entry from level zero to level two to the power m minus one. "
                    + "Natural powers retain the value one at exponent zero, even at zero entries."),
            Thm("pair", "sparse_pair_data", "Sparse states and the supported integer kernel", Pair(),
                "For every natural m at least two, both actual state matrices are positive "
                    + "definite. The distinguished monomial takes opposite values of modulus "
                    + "one twelfth to the power twice m minus one. The entire integer kernel "
                    + "of the two supported gaps consists of multiples of the primitive "
                    + "vector with coordinates m and minus m plus one. Every nonzero multiple "
                    + "has l1 norm at least twice m minus one. The kernel calculation applies "
                    + "the cofactor kernel theorem after checking its determinant, sum and gcd "
                    + "premises for these actual consecutive gaps."),
            Def("energies", "energy", "Integer energy labels",
                "The labelled basis energies are zero, one and m. Integer differences "
                    + "are used before grouping any equal numerical gaps."),
            Def("exponents", "Exponent", "Labelled matrix exponents",
                "An exponent is a natural number at each of the nine ordered matrix "
                    + "coordinates. Opposite directions and repeated numerical gaps "
                    + "remain different coordinates."),
            Def("degree", "degree", "Total exponent degree",
                "The degree is the sum of all nine natural multiplicities."),
            Def("weight", "weight", "Total energy weight",
                "The weight sums each actual ordered energy difference times its "
                    + "natural multiplicity, in the integers."),
            Def("monomials", "monomial", "Actual coordinate monomials",
                "The monomial is the product of all nine matrix entries raised to "
                    + "their natural exponents. In particular zero to the zeroth power "
                    + "is one."),
            Thm("low", "sparse_low_monomials", "Every low zero-weight monomial", Low(),
                "For every m at least two, every labelled exponent of degree less "
                    + "than twice m minus one and weight zero gives the same monomial "
                    + "on the first matrix and on every unit phase in the sparse family. "
                    + "A positive exponent on either missing edge makes both values zero. "
                    + "Otherwise the primitive kernel and the degree bound force both "
                    + "net oriented exponents to vanish, so conjugate phases cancel."),
            Def("coordinate", "coordinateExponent", "One labelled occurrence",
                "The unit exponent at one ordered coordinate retains the row and column labels."),
            Def("tensor-exponent", "tensorExponent", "Exponents of native tensor entries",
                "Each pair of product-basis words contributes one labelled occurrence at each tensor position."),
            Def("total-energy", "totalEnergy", "Total product-basis energy",
                "The energy of a word is the sum of its single-copy energies, with zero for the empty word."),
            Def("projector", "energyProjector", "Complete total-energy projections",
                "The diagonal projection selects all words with the specified total energy. It preserves the full degenerate energy space."),
            Def("pinching", "pinchedCopies", "Pinched native tensor states",
                "Sum the native tensor state between the complete projections over its finite set of total energies."),
            Def("energy-pinch", "energyPinch", "Total-energy pinching of arbitrary matrices",
                "The same complete projections act on arbitrary complex matrices. Pinching a positive contraction gives a positive contraction commuting with the sum Hamiltonian."),
            Thm("compatible-effects", "compatible_effects_iff", "Every compatible complex effect", CompatibleEffects(),
                "For all native density states, including states of deficient rank, equality of complete total-energy pinchings is equivalent to equality of unconditional trace probabilities for every positive complex effect bounded by the identity and commuting with the sum Hamiltonian. Pinching preserves the trace pairing and maps every complex effect into this commutant. The original effect-trace uniqueness theorem then separates the pinched matrices. No reality restriction is placed on the effect entries, and degenerate blocks retain their complex off-diagonals."),
            Thm("tensor-bridge", "tensor_monomial_bridge", "Native tensor entries and total-energy pinching", Tensor(),
                "For every native three-dimensional density state, every copy count and every pair of actual tensor words, "
                    + "the recursively constructed exponent has that copy count as degree and the total-energy difference as weight. "
                    + "The actual tensor entry equals its coordinate monomial. Complete total-energy pinching keeps exactly the "
                    + "zero-weight entries, including off-diagonals inside degenerate blocks. The pinched matrix is positive semidefinite with trace one."),
            Thm("exponent-bridge", "exponent_tensor_bridge", "Every exponent has native tensor words", ExponentBridge(),
                "Every labelled exponent is realized by two words whose length is its degree. "
                    + "Their energy difference is its weight, and their tensor entry is its monomial on every native state. "
                    + "The construction successively removes one actual coordinate occurrence. It includes the empty exponent, "
                    + "zero matrix entries, deficient rank and repeated numerical gaps."),
            Thm("low-pinching", "sparse_low_pinching", "Low-order complete pinchings agree", LowPinching(),
                "For every m at least two and every copy count below twice m minus one, the complete total-energy "
                    + "pinchings of the actual sparse tensor states agree. This uses all labelled entries and includes zero exponents."),
            Def("word-index", "wordIndex", "Tuples in the native tensor basis",
                "A tuple is mapped to the same recursively parenthesized product basis used by the native density-state copies."),
            Def("order", "copyOrder", "Two block lengths",
                "The distinguishing copy count is m plus m minus one."),
            Def("word-i", "wordI", "First distinguishing word",
                "The first word has m twos followed by m minus one zeros."),
            Def("word-j", "wordJ", "Second distinguishing word",
                "The second word has m ones followed by m minus one twos."),
            Def("hamiltonian", "totalHamiltonian", "Sum of the one-copy Hamiltonians",
                "On each native tensor product, add the first Hamiltonian tensored with the identity to the identity tensored with the remaining Hamiltonian."),
            Thm("hamiltonian-diagonal", "total_hamiltonian_diagonal", "The actual sum Hamiltonian is diagonal", HamiltonianDiagonal(),
                "For every m and every native tensor length, the recursive sum Hamiltonian is diagonal in the native product basis. "
                    + "Its diagonal is the sum of the actual one-copy energy labels."),
            Thm("words", "sparse_joint_words", "Actual equal-energy words", Words(),
                "For every m at least two the two words are distinct, have common energy m squared, and have length twice m minus one. "
                    + "Their tensor entry on every native state is the distinguished monomial, without a rank or support restriction."),
            Def("effect", "jointEffect", "Equal-superposition projection",
                "The effect is one half the outer product of the sum of the two computational basis vectors with its conjugate. "
                    + "It is a projection on their actual tensor space."),
            Thm("born", "sparse_joint_effect", "A compatible effect with exact unconditional probabilities", Effect(),
                "The effect and its complement are positive semidefinite, and the effect commutes with the sum Hamiltonian. "
                    + "Its unconditional probabilities on the two native sparse tensor states are respectively one third to the "
                    + "copy count plus and minus one twelfth to that count. Both real probabilities lie between zero and one, "
                    + "and their gap is positive. The complete total-energy pinchings differ at this copy count. "
                    + "At every smaller copy count all compatible complex effects have equal probabilities on the two actual tensor states."),
            Def("indecomposable", "Indecomposable", "Labelled indecomposable zero-weight exponents",
                "An exponent is nonzero, has weight zero, and contains no nonzero proper subexponent of weight zero. "
                    + "This definition retains diagonal coordinates and distinguishes coordinates with equal numerical gaps."),
            Paragraph(Text("For every natural m at least two, let alpha have multiplicity m at the ordered coordinate (2,1), "
                + "multiplicity m minus one at (0,2), and zero at all other coordinates. Its weight is "
                + "m times (m minus one) minus (m minus one) times m, hence zero; its degree is twice m minus one. "
                + "Its monomial on every complex three by three matrix X is exactly X(2,1) to the power m "
                + "times X(0,2) to the power m minus one. These statements keep all nine coordinate labels, "
                + "including the coincident numerical gaps when m equals two.")),
            Paragraph(Text("The indecomposability of alpha follows directly from "
                + "D5/S3/Arith/Lattices/CofactorKernel.primitive_kernel_span. Take the one-row integer matrix "
                + "A with entries m minus one and m, and the primitive vector v with entries m and minus (m minus one). "
                + "The augmented determinant is one, A times v is zero, the coordinate sum of v is one, and its coordinate gcd is one. "
                + "If beta is a nonnegative subexponent of alpha with weight zero, its only possible nonzero coordinates "
                + "are (2,1) and (0,2). The vector (beta(2,1), minus beta(0,2)) lies in the integer kernel of A. "
                + "The cited theorem makes it ell times v. Since zero is at most beta(2,1) and beta(2,1) is at most m, "
                + "the integer ell is zero or one. Thus beta is zero or alpha. The exponent alpha is nonzero, "
                + "so it is an indecomposable zero-weight exponent attaining degree twice m minus one. "
                + "Together with the general labelled degree bound, this gives the exact maximal degree. "
                + "This application uses the original primitive integer-kernel theorem; it supplies no additional "
                + "claim about experimental access to matrix coordinates.")),
            Paragraph(Text("The all-state compact-orbit theorem combines these sparse lower bounds with labelled exponent decomposition "
                + "and phase reconstruction to obtain the least uniform order. The explicit effect gives no Helstrom optimum, adaptive "
                + "protocol bound or postselection advantage. Integer description length and physical copy cost are distinct quantities.")))));

    private static DocumentBlock Def(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static DocumentBlock Thm(string id, string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    private static Formula C(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula P(Formula x, Formula e) => Seq(Open, x, Close, Caret, Grp(e));
    private static Formula A(Formula x) => Seq(Lvert, Sp, x, Rvert, Sp);
    private static Formula Third => Seq(Frac, Grp(D(1)), Grp(D(3)));
    private static Formula Twelfth => Seq(Frac, Grp(D(1)), Grp(D(1, 2)));
    private static Formula Spectrum()
    {
        var u = F.Id("u");
        var x = C("sparseMatrix", u);
        var delta = Seq(Frac, Grp(Sqrt, Grp(D(2))), Grp(D(1, 2)));
        return Disp(Seq(Forall, Sp, u, InMacro, C("Complex"), Comma,
            u, Cdot, Sp, C("star", u), Eq, D(1), Sp, Implies, Sp, RowBreak,
            C("PosDef", x), Sp, Land, Sp, C("trace", x), Eq, D(1), Sp, Land, Sp, RowBreak,
            C("spectrum", C("Complex"), x), Eq, OpenBrace, Sp, Third, Comma,
            Third, Minus, delta, Comma, Third, Plus, delta, CloseBrace));
    }
    private static Formula Pair()
    {
        var m = F.Id("m");
        var k = Seq(F.Id("k"), Underscore, Grp(D(1)));
        var j = Seq(F.Id("k"), Underscore, Grp(D(2)));
        var ell = F.Id("l");
        var pred = Seq(Open, m, Minus, D(1), Close);
        var length = Seq(D(2), Cdot, Sp, m, Minus, D(1));
        var r = C("stateMatrix", C("rho"));
        var s = C("stateMatrix", C("sigma", m));
        return Disp(Seq(Forall, Sp, m, InMacro, C("Nat"), Comma,
            D(2), Leq, Sp, m, Sp, Implies, Sp, RowBreak,
            C("PosDef", r), Sp, Land, Sp, C("PosDef", s), Sp, Land, RowBreak,
            C("starMonomial", m, r), Eq, P(Twelfth, length), Sp, Land, RowBreak,
            C("starMonomial", m, s), Eq, Minus, P(Twelfth, length), Sp, Land, RowBreak,
            Open, Forall, Sp, k, Comma, j, InMacro, C("Int"), Comma,
            Open, pred, Cdot, Sp, k, Plus, m, Cdot, Sp, j, Eq, D(0), Sp, Iff, Sp,
            Exists, Sp, ell, InMacro, C("Int"), Comma,
            k, Eq, ell, Cdot, Sp, m, Sp, Land, Sp, j, Eq, ell, Cdot, Sp, Open, Minus,
            pred, Close, Close, Close, Sp, Land, RowBreak,
            Open, Forall, Sp, ell, InMacro, C("Int"), Comma,
            ell, Neq, Sp, D(0), Sp, Implies, Sp, length, Leq, Sp,
            A(Seq(ell, Cdot, Sp, m)), Plus, A(Seq(ell, Cdot, Sp, Open, Minus, pred, Close)), Close));
    }
    private static Formula Low()
    {
        var m = F.Id("m"); var alpha = F.Id("a"); var u = F.Id("u");
        return Disp(Seq(Forall, Sp, m, InMacro, C("Nat"), Comma,
            D(2), Leq, Sp, m, Sp, Implies, Sp,
            Forall, Sp, alpha, InMacro, C("Exponent"), Comma, RowBreak,
            C("degree", alpha), Lt, D(2), Cdot, Sp, m, Minus, D(1), Sp, Implies, Sp,
            C("weight", m, alpha), Eq, D(0), Sp, Implies, Sp, RowBreak,
            Forall, Sp, u, InMacro, C("Complex"), Comma,
            u, Cdot, Sp, C("star", u), Eq, D(1), Sp, Implies, Sp, RowBreak,
            C("monomial", C("sparseMatrix", D(1)), alpha), Eq,
            C("monomial", C("sparseMatrix", u), alpha)));
    }

    private static Formula Entry(Formula x, Formula i, Formula j) => C("entry", x, i, j);
    private static Formula Length(Formula m) => Seq(D(2), Cdot, Sp, m, Minus, D(1));
    private static Formula Tensor()
    {
        var m = F.Id("m"); var n = F.Id("n"); var r = F.Id("r");
        var i = F.Id("I"); var j = F.Id("J");
        var a = C("tensorExponent", n, i, j);
        var x = C("monomial", C("stateMatrix", r), a);
        var pin = C("pinchedCopies", m, n, r);
        return Disp(Seq(Forall, Sp, m, Comma, n, InMacro, C("Nat"), Comma,
            Forall, Sp, r, InMacro, C("DensityState", C("Fin", D(3))), Comma,
            Forall, Sp, i, Comma, j, InMacro, C("CopyIndex", C("Fin", D(3)), n), Comma, RowBreak,
            C("degree", a), Eq, n, Sp, Land, Sp,
            C("weight", m, a), Eq, C("totalEnergy", m, n, i), Minus, C("totalEnergy", m, n, j), Sp, Land, RowBreak,
            Entry(C("stateMatrix", C("copies", r, n)), i, j), Eq, x, Sp, Land, RowBreak,
            Entry(pin, i, j), Eq, C("ite", Seq(C("weight", m, a), Eq, D(0)), x, D(0)), Sp, Land, RowBreak,
            C("PosSemidef", pin), Sp, Land, Sp, C("trace", pin), Eq, D(1)));
    }
    private static Formula LowPinching()
    {
        var m = F.Id("m"); var n = F.Id("n");
        return Disp(Seq(Forall, Sp, m, Comma, n, InMacro, C("Nat"), Comma,
            D(2), Leq, Sp, m, Sp, Implies, Sp, n, Lt, Length(m), Sp, Implies, Sp,
            C("pinchedCopies", m, n, C("rho")), Eq, C("pinchedCopies", m, n, C("sigma", m))));
    }
    private static Formula ExponentBridge()
    {
        var m = F.Id("m"); var a = F.Id("a"); var i = F.Id("I"); var j = F.Id("J"); var r = F.Id("r");
        var n = C("degree", a); var x = C("monomial", C("stateMatrix", r), a);
        return Disp(Seq(Forall, Sp, m, InMacro, C("Nat"), Comma,
            Forall, Sp, a, InMacro, C("Exponent"), Comma,
            Exists, Sp, i, Comma, j, InMacro, C("CopyIndex", C("Fin", D(3)), n), Comma, RowBreak,
            C("tensorExponent", n, i, j), Eq, a, Sp, Land, Sp,
            C("totalEnergy", m, n, i), Minus, C("totalEnergy", m, n, j), Eq, C("weight", m, a), Sp, Land, RowBreak,
            Forall, Sp, r, InMacro, C("DensityState", C("Fin", D(3))), Comma,
            Entry(C("stateMatrix", C("copies", r, n)), i, j), Eq, x, Sp, Land, RowBreak,
            Entry(C("pinchedCopies", m, n, r), i, j), Eq,
            C("ite", Seq(C("weight", m, a), Eq, D(0)), x, D(0))));
    }
    private static Formula HamiltonianDiagonal()
    {
        var m = F.Id("m"); var n = F.Id("n"); var i = F.Id("I");
        return Disp(Seq(Forall, Sp, m, Comma, n, InMacro, C("Nat"), Comma,
            C("totalHamiltonian", m, n), Eq, C("diagonal", Seq(Open, LambdaLower, Sp, i, Colon,
                C("CopyIndex", C("Fin", D(3)), n), Comma, C("totalEnergy", m, n, i), Close))));
    }
    private static Formula CompatibleEffects()
    {
        var m = F.Id("m"); var n = F.Id("n"); var r = F.Id("r");
        var s = F.Id("s"); var f = F.Id("F");
        var h = C("totalHamiltonian", m, n);
        Formula Prob(Formula x) => C("trace", Seq(f, Cdot, Sp,
            C("stateMatrix", C("copies", x, n))));
        return Disp(Seq(Forall, Sp, m, Comma, n, InMacro, C("Nat"), Comma,
            Forall, Sp, r, Comma, s, InMacro, C("DensityState", C("Fin", D(3))), Comma, RowBreak,
            C("pinchedCopies", m, n, r), Eq, C("pinchedCopies", m, n, s), Sp, Iff, Sp,
            Forall, Sp, f, InMacro, C("Matrix", C("CopyIndex", C("Fin", D(3)), n),
                C("CopyIndex", C("Fin", D(3)), n), C("Complex")), Comma, RowBreak,
            C("PosSemidef", f), Sp, Implies, Sp,
            C("PosSemidef", Seq(D(1), Minus, f)), Sp, Implies, Sp,
            f, Cdot, Sp, h, Eq, h, Cdot, Sp, f, Sp, Implies, Sp,
            Prob(r), Eq, Prob(s)));
    }
    private static Formula Words()
    {
        var m = F.Id("m"); var r = F.Id("r"); var l = C("copyOrder", m);
        var i = C("wordI", m); var j = C("wordJ", m);
        return Disp(Seq(Forall, Sp, m, InMacro, C("Nat"), Comma,
            D(2), Leq, Sp, m, Sp, Implies, Sp, RowBreak,
            l, Eq, Length(m), Sp, Land, Sp, i, Neq, Sp, j, Sp, Land, RowBreak,
            C("totalEnergy", m, l, i), Eq, P(m, D(2)), Sp, Land, Sp,
            C("totalEnergy", m, l, j), Eq, P(m, D(2)), Sp, Land, RowBreak,
            Forall, Sp, r, InMacro, C("DensityState", C("Fin", D(3))), Comma,
            Entry(C("stateMatrix", C("copies", r, l)), i, j), Eq,
            C("starMonomial", m, C("stateMatrix", r))));
    }
    private static Formula Effect()
    {
        var m = F.Id("m"); var l = C("copyOrder", m); var q = C("jointEffect", m);
        var n = F.Id("n"); var f = F.Id("F"); var hn = C("totalHamiltonian", m, n);
        var h = C("totalHamiltonian", m, l); var k = Length(m);
        var r = C("rho"); var s = C("sigma", m);
        var plus = Seq(P(Third, k), Plus, P(Twelfth, k));
        var minus = Seq(P(Third, k), Minus, P(Twelfth, k));
        Formula Prob(Formula x) => C("trace", Seq(q, Cdot, Sp, C("stateMatrix", C("copies", x, l))));
        Formula LowProb(Formula x) => C("trace", Seq(f, Cdot, Sp, C("stateMatrix", C("copies", x, n))));
        return Disp(Seq(Forall, Sp, m, InMacro, C("Nat"), Comma,
            D(2), Leq, Sp, m, Sp, Implies, Sp, RowBreak,
            C("PosSemidef", q), Sp, Land, Sp, C("PosSemidef", Seq(D(1), Minus, q)), Sp, Land, RowBreak,
            q, Cdot, Sp, h, Eq, h, Cdot, Sp, q, Sp, Land, RowBreak,
            Prob(r), Eq, plus, Sp, Land, Sp, Prob(s), Eq, minus, Sp, Land, RowBreak,
            D(0), Lt, D(2), Cdot, Sp, P(Twelfth, k), Sp, Land, RowBreak,
            plus, InMacro, C("Icc", D(0), D(1)), Sp, Land, Sp,
            minus, InMacro, C("Icc", D(0), D(1)), Sp, Land, RowBreak,
            C("pinchedCopies", m, l, r), Neq, Sp, C("pinchedCopies", m, l, s), Sp, Land, RowBreak,
            Forall, Sp, n, InMacro, C("Nat"), Comma, n, Lt, k, Sp, Implies, Sp,
            Forall, Sp, f, InMacro, C("Matrix", C("CopyIndex", C("Fin", D(3)), n),
                C("CopyIndex", C("Fin", D(3)), n), C("Complex")), Comma, RowBreak,
            C("PosSemidef", f), Sp, Implies, Sp,
            C("PosSemidef", Seq(D(1), Minus, f)), Sp, Implies, Sp,
            f, Cdot, Sp, hn, Eq, hn, Cdot, Sp, f, Sp, Implies, Sp,
            LowProb(r), Eq, LowProb(s)));
    }

}
