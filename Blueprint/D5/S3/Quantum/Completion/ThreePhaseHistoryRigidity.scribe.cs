using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class ThreePhaseHistoryRigidityDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.";
    private static Formula M => F.Id("M");
    private static Formula U => F.Id("U");
    private static Formula N => F.Id("N");
    private static Formula X => F.Id("x");
    private static Formula T => F.Id("u");
    private static Formula K => F.Id("k");
    private static Formula C => F.Id("C");
    private static Formula Chi => F.Id("chi");
    private static Formula Three => Call("ZMod", D(3));
    private static Formula Read(Formula a) => Call("f", a);
    private static Formula Child => Seq(X, Sp, Cdot, Sp,
        Call("iterate", U, Call("val", K), T));
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula All(Formula a, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, a, Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula InSet(Formula a) => Seq(a, Sp, InMacro, Sp, N);
    private static Formula Energy(Formula a) => Call("normSq", Read(a));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All ordered finite histories and character orthogonality eliminate a bounded complex Fourier increment.",
        H("Three-Phase History Rigidity"),
        Blocks(
            Entry("three-phase-words", "PhaseWords", "Phase words retain order and multiplicity",
                Seq(Open, Eqn(Call("PhaseWords", D(0)), Call("Unit")), Sp, Land, Sp,
                    All(F.Id("n"), Seq(Mathbb, Grp(F.Id("N"))),
                        Eqn(Call("PhaseWords", Seq(F.Id("n"), Plus, D(1))),
                            Seq(Call("PhaseWords", F.Id("n")), Sp, Times, Sp, Three))), Close),
                "The phase words have cardinality 3^n for every natural n. Distinct words remain distinct indices even when their original magma labels coincide.",
                DescribeRole.Definition),
            Entry("three-phase-ordered-history", "orderedHistory", "Actual original left-bracketed histories",
                HistoryFormula(),
                "The original type M is any MulOneClass. Each child applies its given binary operation once on the right of the existing history. No associativity or commutativity is used, and no depth cap or deduplication is introduced.",
                DescribeRole.Definition),
            Entry("bounded-phase-recursion-vanishes", "bounded_phase_recursion_vanishes",
                "Conditional vanishing from an assumed Fourier recursion", TheoremFormula(),
                "The full telescope is arbitrary M with only a two-sided unit, U:M to M, u:M, a subset N containing 1 and closed under x times U^k u for every x in N and k in ZMod 3, an injective complex additive character chi of ZMod 3, complex functions f and D, and a finite real C bounding normSq(f x) for every x in N. The displayed local recursion is an additional hypothesis. Character orthogonality yields a child energy of 3 times (normSq(f x)+normSq(f u)+normSq(D x)). Induction over every PhaseWords n gives 3^n times (normSq(f 1)+n normSq(f u)) as a lower bound on the total energy. The upper bound is 3^n C. An Archimedean argument forces normSq(f u)=0. AddChar.wInner_cWeight_eq_boole is the reused scalar orthogonality supplier; it imposes a group law only on the phase index.",
                DescribeRole.Theorem),
            Paragraph(Text("This is the conditional history mechanism consumed by RawAnchoredRadicalDescent. That consumer constructs the actual original quotient, derives the Fourier recursion and its uniform bound, and applies this theorem separately to both ordered pairings. The history theorem itself remains conditional on its stated recursion and uniform bound. No independent admission or atom coverage is asserted by this description.")))));

    private static Formula HistoryFormula() => Seq(
        Forall, Sp, M, Colon, Sp, F.Id("Type"), Comma, Sp,
        OpenBracket, Call("MulOneClass", M), CloseBracket, Comma, Sp,
        U, Colon, Sp, M, Sp, To, Sp, M, Comma, Sp,
        T, Colon, Sp, M, Comma, Sp, Open,
        All(F.Id("w"), Call("PhaseWords", D(0)),
            Eqn(Call("orderedHistory", U, T, D(0), F.Id("w")), D(1))), Sp, Land, Sp,
        All(F.Id("n"), Seq(Mathbb, Grp(F.Id("N"))),
            All(F.Id("w"), Call("PhaseWords", F.Id("n")), All(K, Three,
                Eqn(Call("orderedHistory", U, T, Seq(F.Id("n"), Plus, D(1)),
                    Call("pair", F.Id("w"), K)),
                    Seq(Call("orderedHistory", U, T, F.Id("n"), F.Id("w")), Sp,
                        Cdot, Sp, Call("iterate", U, Call("val", K), T)))))), Close);

    private static Formula TheoremFormula()
    {
        Formula closed = All(X, M, Seq(InSet(X), Sp, Rightarrow, Sp,
            All(K, Three, InSet(Child))));
        Formula bounded = All(X, M, Seq(InSet(X), Sp, Rightarrow, Sp,
            Energy(X), Sp, Le, Sp, C));
        Formula recursion = All(X, M, Seq(InSet(X), Sp, Rightarrow, Sp,
            All(K, Three, Eqn(Read(Child), Seq(Read(X), Sp, Plus, Sp,
                Call("chi", K), Read(T), Sp, Plus, Sp,
                Call("chi", Seq(Minus, K)), Call("D", X))))));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula arrow = Seq(M, Sp, To, Sp, complex);
        return Seq(Forall, Sp, M, Colon, Sp, F.Id("Type"), Comma, Sp,
            OpenBracket, Call("MulOneClass", M), CloseBracket, Comma, Sp,
            U, Colon, Sp, M, Sp, To, Sp, M, Comma, Sp,
            T, Colon, Sp, M, Comma, Sp, N, Colon, Sp, Call("Set", M), Comma, Sp,
            Chi, Colon, Sp, Call("AddChar", Three, complex), Comma, Sp,
            F.Id("f"), Comma, Sp, F.Id("D"), Colon, Sp, arrow, Comma, Sp,
            C, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp, Open,
            InSet(D(1)), Sp, Land, Sp, closed, Sp, Land, Sp,
            Call("Injective", Chi), Sp, Land, Sp, bounded, Sp, Land, Sp, recursion,
            Close, Sp, Rightarrow, Sp, Eqn(Read(T), D(0)));
    }

    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula formula, string narrative, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Gid + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(narrative))), role);
}
