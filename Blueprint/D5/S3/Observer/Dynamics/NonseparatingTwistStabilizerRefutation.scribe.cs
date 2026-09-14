using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Dynamics;

internal sealed class NonseparatingTwistStabilizerRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Dynamics/NonseparatingTwistStabilizerRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual genus-two epimorphism separates marked invariance from invariance of a representation up to one common conjugation.",
        H("A nonseparating twist and an inner compensation"),
        Blocks(
            Paragraph(Text("Let Pi be the original genus-two presentation "
                + "<a,b,c,d | [a,b][c,d]=1>. The automorphism T fixes a,c,d and sends b to ba; "
                + "its inverse sends b to ba^-1. Claim asserts, for every group F and every "
                + "surjective homomorphism phi:Pi to F, that existence of one z satisfying "
                + "phi(Tx)=z phi(x) z^-1 for every x is equivalent to phi(a)=1.")),
            Describe.Lean(
                DescribeId.Create("nonseparating-twist-stabilizer-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Negation of the complete genus-two algebraic specialization"),
                StatementSource.FromAuthor(Disp(Call("Not", F.Id("Claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take the dihedral group with r of order four, s of order two "
                        + "and srs=r^-1. Map (a,b,c,d) to (r^2,s,r,1). The two relator "
                        + "commutators are identity. Surjectivity follows because r and s occur "
                        + "as generator images; the proof constructs preimages of both kinds of elements.")),
                    Paragraph(Text("The images after T are (r^2,sr^2,r,1), exactly their simultaneous "
                        + "conjugates by r. Equality on all presentation generators gives equality "
                        + "of the full homomorphisms. However phi(a)=r^2 is nonidentity. "
                        + "The single common conjugator is essential: no separate per-generator "
                        + "choice or pointwise equality is used.")),
                    Paragraph(Text("The source assertion is Banerjee, Mathematische Annalen 392 "
                        + "(2025), 5045-5064, DOI 10.1007/s00208-025-03213-7, Definition 1 "
                        + "and Proposition 3. The geometric-basis identification of T with a "
                        + "nonseparating Dehn twist is explained in the Library note; "
                        + "the current Lean file formalizes the presented-group consequence. "
                        + "This does not refute the paper's main geometric monodromy theorems "
                        + "or solve the general mapping-class congruence conjecture."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[i]);
        }
        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
