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
                    + "second basis vectors vanish. The two entries into the third basis "
                    + "vector have modulus one twelfth, with a unit phase on the first edge. "
                    + "The reverse entries are the complex conjugates in this same basis."),
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
            Paragraph(Text("These matrix and integer-kernel statements do not by themselves "
                + "establish the least uniform copy order on all density states. That conclusion "
                + "also requires the upper bound for all labelled zero-weight exponents, "
                + "the shared Haar average and full total-energy pinching identity, and "
                + "the equivalence with every compatible complex effect. A compact orbit "
                + "is distinct from reachability at one exact time. The sparse monomial "
                + "alone gives no Helstrom optimum, adaptive protocol bound, postselection "
                + "advantage, or identification of integer description length with copy cost.")))));

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

}
