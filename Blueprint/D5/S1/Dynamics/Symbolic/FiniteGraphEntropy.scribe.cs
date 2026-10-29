using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class FiniteGraphEntropyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/FiniteGraphEntropy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite graph languages are compact, closed and invariant under the one-sided shift.",
        H("Finite Graph Languages as Symbolic Systems"),
        Blocks(
            Paragraph(Text(
                "Let V be a finite vertex type with a discrete topology, and let edge be any directed relation on V. "
                + "The one-sided graph language consists of the vertex sequences following edge at every consecutive pair. "
                + "The compactness and shift-invariance results do not require right-totality. "
                + "These are standard facts about finite graph presentations; no literature novelty is claimed.")),
            Describe.Lean(
                DescribeId.Create("natural-adjacency-matrix"),
                DeclarationHandle.Create(Owner + "adjacency"),
                H("The natural adjacency matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "adjacency(edge) is the V by V matrix over the natural numbers whose entry at (i,j) is 1 when edge(i,j) holds and 0 otherwise. "
                    + "This module defines the matrix but does not yet prove a formula relating its powers to realized prefix counts."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("right-total-extension-condition"),
                DeclarationHandle.Create(Owner + "RightTotal"),
                H("Every vertex has an outgoing edge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "RightTotal(edge) means that for every v there exists w with edge(v,w). "
                    + "A private helper uses this condition to extend each nonempty finite edge path to an infinite path."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("one-sided-edge-language"),
                DeclarationHandle.Create(Owner + "edgeLanguage"),
                H("The graph language with vertex labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "edgeLanguage(edge) specializes FiniteObservationSofic.graphLanguage to the identity vertex labelling. "
                    + "Thus its elements are exactly the sequences w with edge(w(n),w(n+1)) for every natural n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-edge-language-compact-closed"),
                DeclarationHandle.Create(Owner + "edgeLanguage_isCompact_isClosed"),
                H("The language is compact and closed"),
                StatementSource.FromAuthor(new Formula.Logic(
                    Call("IsCompact", Call("edgeLanguage", Id("edge"))),
                    FormulaLogicOperator.And,
                    Call("IsClosed", Call("edgeLanguage", Id("edge"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each consecutive-edge constraint is closed because the finite vertex space is discrete. "
                    + "Their intersection is closed in the compact product V^N, hence compact. "
                    + "The identity-labelled language is its continuous image, and compact subsets of this Hausdorff product are closed. "
                    + "The conclusion includes empty languages and graphs with dead vertices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-edge-language-shift-invariant"),
                DeclarationHandle.Create(Owner + "edgeLanguage_shift_invariant"),
                H("Dropping the first vertex preserves the language"),
                StatementSource.FromAuthor(Call("MapsTo",
                    Call("FullShift.shift", Num(1)),
                    Call("edgeLanguage", Id("edge")),
                    Call("edgeLanguage", Id("edge")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a path satisfies every consecutive-edge constraint, its tail does too. "
                    + "The theorem proves forward invariance under the one-step shift; it does not assert surjectivity of that shift or an entropy formula."))),
                DescribeRole.Theorem))));
}
