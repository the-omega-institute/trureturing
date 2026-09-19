using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class HughesIterationDepthNoGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/HughesIterationDepthNoGap.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/hughes2026a27755");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal fixed-degree insertion has a gap-free spectrum of minimum iteration depths.",
        H("Iteration-Depth No-Gap for Literal Insertion"),
        Blocks(
            Paragraph(Text(
                "Hughes defines k-insertion by interleaving k source factors with k+1 base "
                    + "factors, allowing every factor to be empty. Iteration keeps the same "
                    + "positive degree throughout a history. The result below settles the "
                    + "arbitrary-language conjecture stated in Section 10, not the finite-language "
                    + "Theorem 8 or the insertion-degree conjecture in Section 11.")),
            Node("Language", "Languages of finite words", LanguageFormula(),
                "A language over an alphabet is an arbitrary set of finite lists. No finiteness "
                    + "condition is imposed on the language itself.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("fixedDegreeInsertion", "Literal fixed-degree insertion", InsertionFormula(),
                "A list of k pairs records x_i and y_i, and the final tail records x_(k+1). "
                    + "The x-pieces concatenate to a base word, the y-pieces concatenate to a "
                    + "source word, and pairwise interleaving followed by the tail is the output. "
                    + "Empty lists are allowed in every position.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("fixedDegreeIterate", "Iteration at one fixed degree", IterateFormula(),
                "Stage zero is B. Every successor inserts A into the preceding stage using the "
                    + "same degree k.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("appearsAt", "Appearance at an iteration stage", AppearsFormula(),
                "A word appears at stage m when one positive degree k produces it at that stage. "
                    + "The existential degree may depend on the word and stage.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("hasIterationDepth", "Minimum iteration depth", DepthFormula(),
                "Depth m means appearance at m together with nonappearance at every smaller "
                    + "stage, exactly retaining the minimum convention from the source.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("iterationDepthSpectrum", "Attained minimum depths", SpectrumFormula(),
                "The spectrum contains exactly those natural numbers realized as the minimum "
                    + "iteration depth of some finite word.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("closedSourceZero", "The source depth origin", SourceZeroFormula(),
                "The published minimum depth is zero-based. This Fin 2 value is the actual source "
                    + "coordinate used by the theorem and its finite information arena.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("iterationDepthSpectrumAt", "Spectrum at a selected origin", SpectrumAtFormula(),
                "Changing the origin adds its natural coordinate to every actual minimum depth. "
                    + "At closedSourceZero this is extensionally equal to the published spectrum.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("result", "No gaps in the arbitrary-language spectrum", ResultFormula(),
                "For every finite alphabet and arbitrary languages A and B, any attained depth r "
                    + "forces every q at most r to be attained. From a minimum-depth successor "
                    + "word, the proof extracts its predecessor. If that predecessor appeared too "
                    + "early at degree j, both histories lift to max(k,j) by padding with empty "
                    + "factor pairs, producing the original word too early. Induction then descends "
                    + "through every smaller depth. The argument includes empty languages, "
                    + "epsilon-only languages, and empty alphabets.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hughes-iteration-depth-no-gap"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(CanonicalId(name)), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static string CanonicalId(string name) => name switch
    {
        "Language" => "language",
        "fixedDegreeInsertion" => "fixed-degree-insertion",
        "fixedDegreeIterate" => "fixed-degree-iterate",
        "appearsAt" => "appears-at",
        "hasIterationDepth" => "has-iteration-depth",
        "iterationDepthSpectrum" => "iteration-depth-spectrum",
        "closedSourceZero" => "closed-source-zero",
        "iterationDepthSpectrumAt" => "iteration-depth-spectrum-at",
        "result" => "result",
        _ => throw new ArgumentOutOfRangeException(nameof(name)),
    };

    private static Formula LanguageFormula()
    {
        Formula alpha = F.Id("alpha");
        return Disp(All("alpha", Type(),
            Equal(Call("Language", alpha), Call("Set", Call("List", alpha)))));
    }

    private static Formula InsertionFormula()
    {
        Formula alpha = F.Id("alpha"), k = F.Id("k"), source = F.Id("A"), basis = F.Id("B");
        Formula word = F.Id("w"), pieces = F.Id("pieces"), tail = F.Id("tail");
        Formula pairLists = Call("List", Call("Prod", Call("List", alpha), Call("List", alpha)));
        Formula conditions = And(Member(Call("baseWord", pieces, tail), basis),
            And(Member(Call("sourceWord", pieces), source),
                Equal(Call("pairOutput", pieces, tail), word)));
        Formula witness = Exists("pieces", pairLists,
            And(Equal(Call("length", pieces), k),
                Exists("tail", Call("List", alpha), conditions)));
        return Disp(All("alpha", Type(), All("k", Naturals(),
            All("A", Call("Language", alpha), All("B", Call("Language", alpha),
                All("w", Call("List", alpha),
                    Iff(Member(word, Call("fixedDegreeInsertion", k, source, basis)), witness)))))));
    }

    private static Formula IterateFormula()
    {
        Formula alpha = F.Id("alpha"), k = F.Id("k"), source = F.Id("A"), basis = F.Id("B");
        Formula stage = F.Id("m");
        Formula zero = Equal(Call("fixedDegreeIterate", k, source, basis, D(0)), basis);
        Formula successor = All("m", Naturals(),
            Equal(Call("fixedDegreeIterate", k, source, basis, Plus(stage, D(1))),
                Call("fixedDegreeInsertion", k, source,
                    Call("fixedDegreeIterate", k, source, basis, stage))));
        return Disp(All("alpha", Type(), All("k", Naturals(),
            All("A", Call("Language", alpha), All("B", Call("Language", alpha),
                And(zero, successor))))));
    }

    private static Formula AppearsFormula()
    {
        Formula alpha = F.Id("alpha"), source = F.Id("A"), basis = F.Id("B");
        Formula word = F.Id("w"), stage = F.Id("m"), degree = F.Id("k");
        Formula witness = Exists("k", Naturals(),
            And(Less(D(0), degree),
                Member(word, Call("fixedDegreeIterate", degree, source, basis, stage))));
        return Disp(All("alpha", Type(), All("A", Call("Language", alpha),
            All("B", Call("Language", alpha), All("w", Call("List", alpha),
                All("m", Naturals(),
                    Iff(Call("appearsAt", source, basis, word, stage), witness)))))));
    }

    private static Formula DepthFormula()
    {
        Formula alpha = F.Id("alpha"), source = F.Id("A"), basis = F.Id("B");
        Formula word = F.Id("w"), stage = F.Id("m"), earlier = F.Id("n");
        Formula minimum = And(Call("appearsAt", source, basis, word, stage),
            All("n", Naturals(), Implies(Less(earlier, stage),
                new Formula.Not(Call("appearsAt", source, basis, word, earlier)))));
        return Disp(All("alpha", Type(), All("A", Call("Language", alpha),
            All("B", Call("Language", alpha), All("w", Call("List", alpha),
                All("m", Naturals(),
                    Iff(Call("hasIterationDepth", source, basis, word, stage), minimum)))))));
    }

    private static Formula SpectrumFormula()
    {
        Formula alpha = F.Id("alpha"), source = F.Id("A"), basis = F.Id("B");
        Formula stage = F.Id("m"), word = F.Id("w");
        return Disp(All("alpha", Type(), All("A", Call("Language", alpha),
            All("B", Call("Language", alpha), All("m", Naturals(),
                Iff(Member(stage, Call("iterationDepthSpectrum", source, basis)),
                    Exists("w", Call("List", alpha),
                        Call("hasIterationDepth", source, basis, word, stage))))))));
    }

    private static Formula SourceZeroFormula() =>
        Disp(Equal(F.Id("closedSourceZero"), D(0)));

    private static Formula SpectrumAtFormula()
    {
        Formula alpha = F.Id("alpha"), origin = F.Id("origin");
        Formula source = F.Id("A"), basis = F.Id("B"), shifted = F.Id("n"), stage = F.Id("m");
        Formula witness = Exists("m", Naturals(),
            And(Member(stage, Call("iterationDepthSpectrum", source, basis)),
                Equal(shifted, Plus(stage, Call("val", origin)))));
        return Disp(All("alpha", Type(), All("origin", Call("Fin", D(2)),
            All("A", Call("Language", alpha), All("B", Call("Language", alpha),
                All("n", Naturals(),
                    Iff(Member(shifted, Call("iterationDepthSpectrumAt", origin, source, basis)),
                        witness)))))));
    }

    private static Formula ResultFormula()
    {
        Formula alpha = F.Id("alpha"), source = F.Id("A"), basis = F.Id("B");
        Formula r = F.Id("r"), q = F.Id("q");
        Formula spectrum = Call("iterationDepthSpectrumAt", F.Id("closedSourceZero"), source, basis);
        Formula closure = All("q", Naturals(), Implies(AtMost(q, r), Member(q, spectrum)));
        return Disp(All("alpha", Type(), Implies(Call("Finite", alpha),
            All("A", Call("Language", alpha), All("B", Call("Language", alpha),
                All("r", Naturals(), Implies(Member(r, spectrum), closure)))))));
    }

    private static Formula Type() => Seq(Operatorname, Grp(F.Id("Type")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Plus(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
