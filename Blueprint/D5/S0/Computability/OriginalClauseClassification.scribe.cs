using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class OriginalClauseClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional completeness of the exact original guarded languages.",
        H("Original guarded UNSAT and the ordered UNSAT-SAT pair"),
        Blocks(Describe.Lean(
            DescribeId.Create("original-ftc-lemma63"),
            DeclarationHandle.Create("D5/S0/Computability/OriginalClauseClassification.lemma63"),
            H("One original SAT premise"),
            StatementSource.FromAuthor(Imp(Call("NPComplete", Id("S")),
                And(Call("CoNPComplete", Id("U")), Call("DPComplete", Id("Q"))))),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
            Blocks(
                Paragraph(Text(
                    "S is satisfiability on the original unrestricted formulaWord bytes, with "
                    + "canonical positive binary variable names and assignments on Appearing names. "
                    + "U contains only well-formed words outside S. Q encodes U first and S second "
                    + "by pairWords(u,v)=1^|u|0uv. Empty conjunctions, empty clauses, arbitrary finite "
                    + "clause and name widths, repetitions and tautologies retain these semantics. "
                    + "The sole hypothesis is NP-completeness of this exact S in the finite binary "
                    + "single-tape model. No other CNF language or machine certificate is a premise.")),
                Paragraph(Text(
                    "The finite lexical scanner is related to the exact original decoder. A false "
                    + "fallback repairs malformed outputs of SAT reductions while preserving SAT; "
                    + "a true fallback makes guarded UNSAT exactly complement SAT after repair. "
                    + "These directions differ because malformed words belong to complement SAT "
                    + "and belong to neither original guarded language. Each repair preserves "
                    + "valid input bytes and executes as a total polynomial transducer.")),
                Paragraph(Text(
                    "NP membership is transported by an executed preimage verifier that preserves "
                    + "both decisions and checks the target witness bound at the transformed "
                    + "instance length. Exact polynomial outer projections and the two repairs "
                    + "split Q into an NP factor and a coNP factor. DP means intersections of "
                    + "languages from those two classes.")),
                Paragraph(Text(
                    "For coNP hardness, a reduction of the complement source language to S is "
                    + "followed by false repair, so all outputs are well formed. For a DP source "
                    + "X intersect Y, reduce complement Y and X to S and false-repair both outputs. "
                    + "The common-input pairing transducer evaluates both maps on the same raw "
                    + "input and puts the complement-Y output first. Its ordered output belongs "
                    + "to Q exactly when the source input lies in X intersect Y. All maps are "
                    + "total on raw binary words and are measured by actual finite-machine "
                    + "instructions. The conditional theorem makes no assertion that the original "
                    + "NP-completeness hypothesis has itself been established here."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/OriginalClauseGuard")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/OriginalPairLanguages")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/NPPreimage")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/TransducerPair"))]));

    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
