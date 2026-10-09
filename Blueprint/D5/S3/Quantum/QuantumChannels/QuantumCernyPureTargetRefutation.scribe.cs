using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class QuantumCernyPureTargetRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/lee2026quantumcerny");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pure-target quantum Cerny complexity grows linearly on constant binary words. "
            + "The word consisting of m zeros has complexity m+1, so no uniform square-root bound holds.",
        H("Pure targets prevent general square-root savings"),
        Blocks(
            Node("pure-instance", "Pure-output instances", "HasPureInstance", InstanceFormula(),
                "Two completely positive trace-preserving channels and a start density make w "
                    + "the unique shortest synchronizing word. Every reachable density has the same "
                    + "output P under w, and P equals the outer product of a vector with its adjoint. "
                    + "Since P has trace one, the vector has unit norm.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pure-complexity", "Pure-target complexity", "qcPure", ComplexityFormula(),
                "Take the infimum of the natural dimensions admitting a pure-output instance. "
                    + "For constant words the set is nonempty, so this infimum is attained.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("saving", "The proposed square-root saving", "claim", ClaimFormula(),
                "There would be a real constant C and a natural length threshold such that "
                    + "every binary word beyond that threshold has pure-target complexity "
                    + "at most C times the square root of its length.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("realization", "A realization for every constant word", "constant_word_realization",
                Disp(All("m", Nat(), Call("HasPureInstance", Add(F.Id("m"), D(1)), Zeros(F.Id("m"))))),
                "In dimension m+1 start at the last basis projector. The zero channel has "
                    + "Kraus operators taking basis vector j to its predecessor, with zero fixed; "
                    + "the one channel is the identity. Their Kraus completeness gives trace "
                    + "preservation and complete positivity. A word with z zeros sends basis "
                    + "projector j to max(j-z,0). All basis projectors are reachable, and "
                    + "synchronization is equivalent to z being at least m. Only the all-zero "
                    + "word of length m synchronizes among words of length at most m, and its "
                    + "output is the first basis projector.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("dimension", "The pure-output dimension obstruction", "pure_constant_word_dimension",
                DimensionFormula(),
                "Let the all-zero word of length m be the unique shortest synchronizing word, "
                    + "with pure common output P. Invariance of reachable states under the zero "
                    + "channel implies that P is fixed. The positive functional measuring "
                    + "mass in the orthogonal complement of P vanishes precisely on nonnegative "
                    + "scalar multiples of P. The vanishing vectors of its iterates form "
                    + "subspaces. Decomposing a positive matrix into rank-one terms shows "
                    + "that equality of successive subspaces propagates to the next pair. "
                    + "For m greater than zero, some reachable state fails to reach P at m-1 steps, so every pair "
                    + "up to level m differs. These m strict increases start from a nonzero "
                    + "subspace and force d to be at least m+1, using only positivity and "
                    + "trace preservation of the zero channel. When m is zero, the existence "
                    + "of a density already forces d to be at least one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("exact-value", "The exact constant-word complexity", "constant_word_complexity",
                Disp(All("m", Nat(), Eq(Call("qcPure", Zeros(F.Id("m"))), Add(F.Id("m"), D(1))))),
                "The construction gives dimension m+1. Positivity gives increasing subspaces "
                    + "of vectors whose rank-one matrices reach the pure output line after j "
                    + "zero steps. Equality of successive subspaces propagates to all later "
                    + "levels. For m greater than zero, failure to synchronize at m-1 forces m strict "
                    + "increases from a nonzero initial subspace, requiring dimension at least m+1. "
                    + "At m equal to zero, the existence of a density requires positive dimension.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("refutation", "The general saving fails", "result", Disp(new Formula.Not(F.Id("claim"))),
                "Given a constant C and a length threshold, choose a natural m larger than "
                    + "C squared, the threshold and one. The exact value m+1 exceeds C times "
                    + "the square root of m. Hence no such bound holds for all sufficiently "
                    + "long binary words.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lee-kjoshanssen-2026-quantum-cerny-pure-target"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("qcpure-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Real() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula Words() => Call("List", Call("Fin", D(2)));
    private static Formula States(Formula d) => Call("DensityState", Call("Fin", d));
    private static Formula Channels(Formula d) => new Formula.TypeArrow(Call("Fin", D(2)),
        Call("QuantumChannel", Call("Fin", d), Call("Fin", d)));
    private static Formula Zeros(Formula m) => Call("replicate", m, D(0));

    private static Formula InstanceFormula()
    {
        var d = F.Id("d"); var w = F.Id("w"); var a = F.Id("A");
        var rho0 = F.Id("rho0"); var p = F.Id("P"); var rho = F.Id("rho");
        var output = All("rho", States(d), Imp(
            Call("member", rho, Call("reachable", a, rho0)),
            Eq(Call("applyWord", a, w, rho), p)));
        var instance = Some("A", Channels(d), Some("rho0", States(d), Some("P", States(d),
            And(Call("UniqueShortestSync", a, rho0, w), And(Call("IsPure", p), output)))));
        return Disp(All("d", Nat(), All("w", Words(), Iff(Call("HasPureInstance", d, w), instance))));
    }

    private static Formula DimensionFormula()
    {
        var d = F.Id("d"); var m = F.Id("m"); var a = F.Id("A");
        var rho0 = F.Id("rho0"); var p = F.Id("P"); var rho = F.Id("rho");
        var output = All("rho", States(d), Imp(
            Call("member", rho, Call("reachable", a, rho0)),
            Eq(Call("applyWord", a, Zeros(m), rho), p)));
        var hypothesis = And(Call("UniqueShortestSync", a, rho0, Zeros(m)),
            And(Call("IsPure", p), output));
        return Disp(All("d", Nat(), All("m", Nat(), All("A", Channels(d),
            All("rho0", States(d), All("P", States(d), Imp(hypothesis, Le(Add(m, D(1)), d))))))));
    }

    private static Formula ComplexityFormula()
    {
        var d = F.Id("d"); var w = F.Id("w");
        var set = Seq(Esc, OpenBrace, d, Sp, Colon, Sp, Nat(), Sp, Mid, Sp,
            Call("HasPureInstance", d, w), Esc, CloseBrace);
        return Disp(All("w", Words(), Eq(Call("qcPure", w), Call("sInf", set))));
    }

    private static Formula ClaimFormula()
    {
        var c = F.Id("C"); var m0 = F.Id("m0"); var w = F.Id("w");
        var length = Call("length", w);
        return Disp(Iff(F.Id("claim"), Some("C", Real(), Some("m0", Nat(), All("w", Words(),
            Imp(Le(m0, length), Le(Call("castReal", Call("qcPure", w)),
                Mul(c, Call("sqrt", Call("castReal", length))))))))));
    }
}
