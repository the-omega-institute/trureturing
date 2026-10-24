using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class CoherenceBreakingAmendmentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/yang2018coherencebreaking");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every incoherent trace-preserving Kraus channel of finite coherence-breaking index at least two admits one unitary conjugation repeated between its successive applications.",
        H("Amending coherence-breaking iterates with one unitary"),
        Blocks(
            Paragraph(Text("All matrices are complex and use the fixed incoherent basis indexed by Fin d. The superscript H denotes conjugate transpose, tr is the matrix trace, and a superscript [m] denotes m-fold function iteration. Subtraction in an iteration count is natural-number subtraction.")),
            Node("off-diagonal", "Erasing the diagonal", OffDiagonalFormula(),
                "offDiag", DescribeRole.Definition, AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complex linear map offDiag replaces each diagonal entry by zero and preserves every other matrix entry.")))),
            Node("incoherent-kraus", "Incoherent Kraus operators", IncoherentFormula(),
                "IsIncoherentKraus", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Section 2 calls a Kraus representation incoherent when each individual Kraus operator preserves incoherence on every incoherent input. Equivalently, each column of every Kraus operator has support in at most one row: each basis vector is sent to a scalar multiple of a basis vector. This predicate imposes no trace-preservation condition.")))),
            Node("coherence-breaking", "Coherence-breaking maps", BreakingFormula(),
                "IsCoherenceBreaking", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The output of every positive semidefinite matrix of trace one has zero entries away from the diagonal. This is the coherence-breaking condition of Section 2. The predicate itself is defined for every matrix-valued function; in the conjecture it is applied to quantum channels and their composites.")))),
            Node("amended", "The same conjugation between successive channels", AmendedFormula(),
                "amended", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The composition in Section 5 has n copies of the channel and n minus one copies of the same conjugation when n is at least one. The definition also includes n = 0 through natural-number subtraction. For the finite dimensions used here, the Kraus action and matrix conjugation are given by the following formulas. No normalization of K or unitarity of U is needed to define these maps.")),
                    new DocumentBlock.DisplayFormula(KrausActionFormula()),
                    new DocumentBlock.DisplayFormula(ConjugationFormula()))),
            Node("claim", "The finite-index amendment conjecture", ClaimDefinitionFormula(),
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Section 5 conjectures amendment for incoherent trace-preserving Kraus channels with coherence-breaking index n at least two. The n-th iterate is coherence-breaking, and none of the iterates with 1 <= k < n is coherence-breaking, as in the minimum defining the index in Section 2, Eq. (1). There is one unitary U whose conjugation, inserted in every intervening slot, makes the composite fail to be coherence-breaking. Trace preservation is the Kraus completeness equality below.")),
                    new DocumentBlock.DisplayFormula(KrausChannelFormula()))),
            Describe.Lean(DescribeId.Create("coherence-breaking-amendment-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A permutation with fourth-root phases amends the channel"),
                StatementSource.FromAuthor(Disp(Named("claim"))), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Write Phi for the Kraus channel, let P erase the diagonal entries of a matrix, and put T = P composed with Phi. Incoherence implies that T kills every diagonal matrix, so T = T composed with P. Choose a permutation sigma and phases omega(c) in {1,i,-1,-i}; the unitary U sends the c-th basis vector to omega(c) times the sigma(c)-th basis vector. Its conjugation Lambda commutes with P. The off-diagonal part of the amended composite is (T Lambda)^(n-1) T.")),
                    Paragraph(Text("If that composite were coherence-breaking, this linear map would vanish on every density matrix. Density matrices span the Hermitian matrices over the reals, and every complex matrix is a Hermitian matrix plus i times a Hermitian matrix, so the map would vanish identically. Multiplication on the right by Lambda then gives (T Lambda)^n = 0. Nilpotency forces Tr(T Lambda) = 0, where Tr is the trace of a linear endomorphism of the matrix space.")),
                    Paragraph(Text("Minimality of n >= 2 implies that Phi itself is not coherence-breaking, hence T is nonzero. Since T kills diagonal matrices and has only off-diagonal outputs, there are a != b and k != l for which the (k,l) entry of T(E_ab) is nonzero. Choose sigma with sigma(k) = a and sigma(l) = b. The weighted sum of Tr(T Lambda) over all fourth-root phase assignments, with weight conjugate(omega(k)) omega(l), is 4^d times that nonzero entry. Orthogonality of the phase characters therefore supplies a unitary for which Tr(T Lambda) is nonzero. This contradicts the trace forced by coherence-breaking and proves the conjecture."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("yang-chen-li-fei-wang-2018-coherence-breaking-amendment"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula,
        string declaration, DescribeRole role, AssessedProvenance provenance, BlockSequence prose) =>
        Describe.Lean(DescribeId.Create("coherence-breaking-amendment-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, prose, role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name)
    {
        var parts = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(V(part));
        }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula At(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Field(string name) => Seq(Mathbb, Grp(V(name)));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Mat(Formula d) => Call("Matrix", Fin(d), Fin(d), Field("C"));
    private static Formula Fun(Formula domain, Formula range) => new Formula.TypeArrow(domain, range);
    private static Formula Family(Formula d, Formula r) => Fun(Fin(r), Mat(d));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula NotEqual(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula AtMost(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Less(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula IffOf(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula Adjoint(Formula x) => new Formula.Power(Parenthesized(x), V("H"));
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(Parenthesized(x), FormulaBinaryOperator.Multiply, Parenthesized(y));
    private static Formula Compose(Formula x, Formula y) =>
        Seq(Parenthesized(x), Sp, Circ, Sp, Parenthesized(y));
    private static Formula Iterate(Formula f, Formula n) =>
        new Formula.Power(Parenthesized(f), Seq(OpenBracket, n, CloseBracket));
    private static Formula SumOver(string name, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Parenthesized(Seq(V(name), Colon, domain))),
            Sp, Parenthesized(body));
    private static Formula Conjugation(Formula u) => Call("LinearMap.mulLeftRight", Field("C"),
        Parenthesized(Seq(u, Comma, Sp, Adjoint(u))));
    private static Formula KrausBinders(Formula body) =>
        All("d", Field("N"), All("r", Field("N"), All("K", Family(V("d"), V("r")), body)));

    private static Formula OffDiagonalFormula()
    {
        Formula entry = At(Call("offDiag", V("X")), V("i"), V("j"));
        Formula action = And(
            Implies(Equal(V("i"), V("j")), Equal(entry, D(0))),
            Implies(NotEqual(V("i"), V("j")), Equal(entry, At(V("X"), V("i"), V("j")))));
        return Disp(All("d", Field("N"), All("X", Mat(V("d")),
            All("i", Fin(V("d")), All("j", Fin(V("d")), action)))));
    }

    private static Formula IncoherentFormula()
    {
        Formula zero = Equal(At(V("K"), V("s"), V("i"), V("j")), D(0));
        Formula support = All("i", Fin(V("d")), Implies(NotEqual(V("i"), V("k")), zero));
        Formula columns = All("s", Fin(V("r")), All("j", Fin(V("d")), Ex("k", Fin(V("d")), support)));
        return Disp(KrausBinders(IffOf(Call("IsIncoherentKraus", V("K")), columns)));
    }

    private static Formula BreakingFormula()
    {
        Formula zero = Equal(At(At(V("Phi"), V("rho")), V("i"), V("j")), D(0));
        Formula diagonal = All("i", Fin(V("d")), All("j", Fin(V("d")),
            Implies(NotEqual(V("i"), V("j")), zero)));
        Formula states = All("rho", Mat(V("d")), Implies(Call("PosSemidef", V("rho")),
            Implies(Equal(Call("tr", V("rho")), D(1)), diagonal)));
        return Disp(All("d", Field("N"), All("Phi", Fun(Mat(V("d")), Mat(V("d"))),
            IffOf(Call("IsCoherenceBreaking", V("Phi")), states))));
    }

    private static Formula KrausActionFormula()
    {
        Formula ks = At(V("K"), V("s"));
        Formula sum = SumOver("s", Fin(V("r")), Mul(Mul(ks, V("X")), Adjoint(ks)));
        return KrausBinders(All("X", Mat(V("d")), Equal(Call("krausApply", V("K"), V("X")), sum)));
    }

    private static Formula ConjugationFormula()
    {
        Formula action = Equal(At(Conjugation(V("U")), V("X")),
            Mul(Mul(V("U"), V("X")), Adjoint(V("U"))));
        return All("d", Field("N"), All("U", Mat(V("d")), All("X", Mat(V("d")), action)));
    }

    private static Formula AmendedFormula()
    {
        Formula phi = Call("krausApply", V("K"));
        Formula count = new Formula.Binary(V("n"), FormulaBinaryOperator.Subtract, D(1));
        Formula composite = Compose(phi, Iterate(Compose(Conjugation(V("U")), phi), count));
        Formula identity = Equal(Call("amended", V("K"), V("U"), V("n")), composite);
        return Disp(KrausBinders(All("U", Mat(V("d")), All("n", Field("N"), identity))));
    }

    private static Formula KrausChannelFormula()
    {
        Formula ks = At(V("K"), V("s"));
        Formula completeness = Equal(SumOver("s", Fin(V("r")), Mul(Adjoint(ks), ks)), D(1));
        return KrausBinders(IffOf(Call("IsKrausChannel", V("K")), completeness));
    }

    private static Formula ClaimDefinitionFormula()
    {
        Formula phi = Call("krausApply", V("K"));
        Formula minimal = All("k", Field("N"), Implies(AtMost(D(1), V("k")),
            Implies(Less(V("k"), V("n")),
                new Formula.Not(Parenthesized(Call("IsCoherenceBreaking", Iterate(phi, V("k"))))))));
        Formula unitary = new Formula.Relation(V("U"), FormulaRelationOperator.MemberOf,
            Call("Matrix.unitaryGroup", Fin(V("d")), Field("C")));
        Formula conclusion = Ex("U", Mat(V("d")), And(unitary,
            new Formula.Not(Parenthesized(Call("IsCoherenceBreaking",
                Call("amended", V("K"), V("U"), V("n")))))));
        Formula body = KrausBinders(Implies(Call("IsKrausChannel", V("K")),
            Implies(Call("IsIncoherentKraus", V("K")), All("n", Field("N"),
                Implies(AtMost(D(2), V("n")),
                    Implies(Call("IsCoherenceBreaking", Iterate(phi, V("n"))),
                        Implies(minimal, conclusion)))))));
        return Disp(IffOf(Named("claim"), body));
    }
}
