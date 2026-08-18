using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Irrationality;

internal sealed class CubicConjugateTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var statement = Call("Irrational",
            Subtract(Num(1), Id("tribonacciConstant")));

        const string declarationPrefix = "D5/S3/Constants/Irrationality/CubicConjugateTrace.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The two non-Perron roots sum to one minus the base, which is irrational.",
            H("Conjugate Trace"),
            Blocks(
                Paragraph(Text(
                    "The three roots of the cubic sum to one, an integer. Splitting off the "
                        + "Perron factor leaves a quadratic whose linear coefficient reads off "
                        + "the sum of the other two roots: one minus the base. That number is "
                        + "irrational, so the expanding root does not sit in a rational trace "
                        + "relation with the contracting pair.")),
                Paragraph(Text(
                    "This is what separates the cubic from the quadratic case. There the two "
                        + "roots are the whole conjugate set and their sum is an integer; here "
                        + "the dominant root alone carries no such relation, and the integrality "
                        + "that the quadratic tower enjoys is a privilege of having exactly two "
                        + "faces.")),
                Describe.Lean(
                    DescribeId.Create("the-perron-root-does-not-carry-the-trace"),
                    DeclarationHandle.Create(
                        declarationPrefix + "cubic_trace_is_not_carried_by_the_perron_root"),
                    H("The Perron root does not carry the trace"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The factorisation was already in the tree; the sum of roots was not, "
                            + "and neither was the irrationality of the base, which landed "
                            + "separately in the same session. Without it this conclusion has no "
                            + "proof, which is how an unproved obvious fact blocks a whole "
                            + "downstream line rather than a single lemma."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/Tribonacci/Binet")),
            ]));
    }
}
