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
    private static Formula Three => Call("ZMod", D(3));
    private static Formula Child => Seq(X, Sp, Cdot, Sp,
        Call("iterate", U, Call("val", K), T));
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula All(Formula a, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, a, Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula InSet(Formula a) => Seq(a, Sp, InMacro, Sp, N);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All ordered finite histories supply an energy-growth estimate; raw comparison balance yields marker readouts.",
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
            Entry("history-energy-growth", "history_energy_growth",
                "Energy growth over every ordered history depth", EnergyFormula(),
                "For every original unital magma, a set containing the unit and closed under each of the three original children, a real energy E and increment d, assume 3(E(x)+d)<=sum_k E(x*U^k(u)) on that set. Induction gives the displayed lower bound for every natural depth n. The sum is over every phase word with its original order and multiplicity, even when labels coincide. The bounded-increment proof in RawAnchoredFourierQuotient compares this same sum with 3^n*C, divides by the positive 3^n and uses the Archimedean property. Its Fourier mode consumer is then applied to both actual ordered pairings in RawAnchoredRadicalDescent.",
                DescribeRole.Theorem),
            Paragraph(Text("The cardinality identity phaseWords_card and membership induction history_mem are used in the upper-bound comparison by bounded_energy_increment_nonpos in RawAnchoredFourierQuotient. The cardinality is exactly 3^n, and membership follows for every original ordered history from unit membership and closure under every original phase child.")),
            RawReadouts.Balance(),
            RawReadouts.Marker(),
            Paragraph(Text("The raw law and marker readings feed the ordered Fourier quotient. The ordered energy-growth estimate supplies its bounded-increment and bounded Fourier mode theorems, and the original-domain consumer derives both uniform pairing bounds before applying that theorem twice. The actual original operation is never assumed associative or commutative.")))));

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

    private static Formula EnergyFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula n = F.Id("n");
        Formula word = F.Id("w");
        Formula closed = All(X, M, Seq(InSet(X), Sp, Rightarrow, Sp,
            All(K, Three, InSet(Child))));
        Formula energy(Formula x) => Call("E", x);
        Formula growth = All(X, M, Seq(InSet(X), Sp, Rightarrow, Sp,
            D(3), Sp, Cdot, Sp, Open, energy(X), Sp, Plus, Sp, F.Id("d"), Close,
            Sp, Le, Sp, new Formula.Subscript(Sum, Seq(K, Colon, Sp, Three)), Sp, energy(Child)));
        Formula total = Seq(new Formula.Subscript(Sum,
            Seq(word, Colon, Sp, Call("PhaseWords", n))), Sp,
            energy(Call("orderedHistory", U, T, n, word)));
        Formula lower = Seq(D(3), Caret, Grp(n), Sp, Cdot, Sp, Open,
            energy(D(1)), Sp, Plus, Sp, n, Sp, Cdot, Sp, F.Id("d"), Close);
        return Seq(Forall, Sp, M, Colon, Sp, F.Id("Type"), Comma, Sp,
            OpenBracket, Call("MulOneClass", M), CloseBracket, Comma, Sp,
            U, Colon, Sp, M, Sp, To, Sp, M, Comma, Sp, T, Colon, Sp, M, Comma, Sp,
            N, Colon, Sp, Call("Set", M), Comma, Sp,
            F.Id("E"), Colon, Sp, M, Sp, To, Sp, real, Comma, Sp,
            F.Id("d"), Colon, Sp, real, Comma, Sp,
            Open, InSet(D(1)), Sp, Land, Sp, closed, Sp, Land, Sp, growth, Close,
            Sp, Rightarrow, Sp, All(n, Seq(Mathbb, Grp(F.Id("N"))), Seq(lower, Sp, Le, Sp, total)));
    }

    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula formula, string narrative, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Gid + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(narrative))), role);
    private static class RawReadouts
    {
        private const string Gid = "D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.";
        private static Formula M => F.Id("M");
        private static Formula A => F.Id("a");
        private static Formula B => F.Id("b");
        private static Formula U => F.Id("u");
        private static Formula V => F.Id("v");
        private static Formula Z => F.Id("z");
        private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
        private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
        private static Formula Plus2(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
        private static Formula Three(Formula a) => Seq(D(3), Sp, Cdot, Sp, a);
        private static Formula Product(Formula a, Formula b) => Seq(Open, a, Sp, Cdot, Sp, b, Close);
        private static Formula Mark(Formula a) => Call("U", a);
        private static Formula Read(Formula a, Formula b) => Call("c", a, b);
        private static Formula All(Formula variable, Formula carrier, Formula body) =>
            Seq(Open, Forall, Sp, variable, Colon, Sp, carrier, Comma, Sp, body, Close);
        private static Formula AllM(Formula variable, Formula body) => All(variable, M, body);
        private static Formula Arrow(Formula a, Formula b) => Seq(Open, a, Sp, Rightarrow, Sp, b, Close);
        private static Formula Both(Formula a, Formula b) => Seq(Open, Open, a, Close, Sp, Land, Sp, Open, b, Close, Close);
        private static Formula Sum3(Formula a, Formula b, Formula c) => Plus2(Plus2(a, b), c);
        private static Formula Conjunction(params Formula[] clauses)
        {
            var result = clauses[^1];
            for (var i = clauses.Length - 2; i >= 0; --i)
                result = Both(clauses[i], result);
            return result;
        }

        private static Formula Original(Formula body) => Seq(
            Forall, Sp, M, Colon, Sp, F.Id("Type"), Comma, Sp,
            OpenBracket, Call("MulOneClass", M), CloseBracket, Comma, Sp,
            F.Id("U"), Colon, Sp, M, Sp, To, Sp, M, Comma, Sp,
            F.Id("c"), Colon, Sp, M, Sp, To, Sp, M, Sp, To, Sp, Real, Comma, Sp,
            Arrow(Call("RawBalance", F.Id("U"), F.Id("c")), body));

        internal static DocumentBlock Balance() =>
            Describe.Lean(
                DescribeId.Create("raw-three-phase-balance"),
                DeclarationHandle.Create(Gid + "RawBalance"),
                H("The original raw balance hypotheses"),
                StatementSource.FromAuthor(Disp(Frame(Eqn(Call("RawBalance", F.Id("U"), F.Id("c")),
                    Conjunction(Eqn(Mark(D(1)), D(1)),
                        AllM(A, AllM(B, Seq(D(0), Sp, Le, Sp, Read(A, B)))),
                        AllM(A, Eqn(Read(A, A), D(0))),
                        AllM(A, AllM(B, AllM(U, AllM(V, RawBalanceFormula()))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("M has only a binary operation and a two-sided unit. U is an arbitrary self-map fixing the unit, and c is finite and real-valued. No associativity, commutativity, cancellation, inverse, marker homomorphism, surjectivity, periodicity, symmetry or positive-semidefinite form is assumed."))),
                DescribeRole.Definition);

        internal static DocumentBlock Marker() =>
            Describe.Lean(
                DescribeId.Create("raw-marker-readouts"),
                DeclarationHandle.Create(Gid + "raw_marker_readouts"),
                H("The comparison has derived marker invariance"),
                StatementSource.FromAuthor(Disp(Original(Conjunction(
                    AllM(U, AllM(V, Eqn(Read(Mark(U), Mark(V)), Read(U, V)))),
                    AllM(A, AllM(B, AllM(U, AllM(V,
                        Eqn(Read(Product(A, Mark(Mark(Mark(U)))), Product(B, Mark(Mark(Mark(V))))),
                            Read(Product(A, U), Product(B, V))))))),
                    AllM(U, AllM(Z, Both(
                        Eqn(Read(Mark(Mark(Mark(U))), Z), Read(U, Z)),
                        Eqn(Read(Z, Mark(Mark(Mark(U)))), Read(Z, U))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For s(n)=c(U^n u,U^n v), the raw law at the two units gives s(n+1)+s(n+2)=2s(n). Apply ThreeWayBalance.nonneg_recurrence_constant directly, exchanging the summands. Subtracting consecutive original balance identities gives contextual invariance. Specializing either contextual input to the unit gives every row and column equality. These equalities supply the ordered anchored-kernel descent below. Only the readings have period three; the original marker need not have period three."))),
                DescribeRole.Theorem);
        private static Formula RawBalanceFormula() => Eqn(
            Sum3(Read(Product(A, U), Product(B, V)),
                Read(Product(A, Mark(U)), Product(B, Mark(V))),
                Read(Product(A, Mark(Mark(U))), Product(B, Mark(Mark(V))))),
            Plus2(Three(Read(A, B)), Three(Read(U, V))));

        private static Formula Frame(Formula body) => Seq(
            Forall, Sp, M, Colon, Sp, F.Id("Type"), Comma, Sp,
            OpenBracket, Call("MulOneClass", M), CloseBracket, Comma, Sp,
            F.Id("U"), Colon, Sp, M, Sp, To, Sp, M, Comma, Sp,
            F.Id("c"), Colon, Sp, M, Sp, To, Sp, M, Sp, To, Sp, Real, Comma, Sp, body);
    }

}
