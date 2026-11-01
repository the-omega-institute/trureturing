using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ClassicalADZhangYeungDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/ClassicalADZhangYeung.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete Zhang-Yeung inequality holds on the finite AD-classical family.", H("Zhang-Yeung for Classical AD Density States"),
        Blocks(
            Paragraph(Text("For arbitrary finite nonempty A, B, C, D, every nonnegative p_ad summing to one, and arbitrary density blocks tau_ad on B tensor C, take rho=sum_ad p_ad |a,d><a,d| tensor tau_ad, reordered into ABCD. The theorem proves the full entropy defect is nonnegative. The source of each entropy is an actual marginal density. No SSA, copy entropy, support, full-rank, independent-BC, or strict-positive-weight hypothesis is supplied. This is a conditional theorem on a specified classical AD decomposition; it makes no claim about coherent AD states, arbitrary separable nonorthogonal ensembles, or unrestricted quantum states. No originality or priority claim is made.")),
            Paragraph(Text("The classical reference is Zhang and Yeung, On characterization of entropy function via information inequalities, IEEE Transactions on Information Theory 44(4), 1440-1452, DOI 10.1109/18.681320. The arbitrary-joint-BC statement here is a repository-derived composition of the conditional-copy argument, existing CQ/product entropy and attributed Physlib SSA, including entangled and singular blocks and zero weights. The classical paper is not cited as proving this hybrid quantum statement. Its precise literature priority has not been established here. Library/Divergence/meiburg2026ssa.md gives the source admission, receiving interfaces and classification; no separate AC extension is claimed.")),
            Result("ad-zy", "zhang_yeung_classical_ad", "The AD-classical Zhang-Yeung theorem", "The physical E copy is constructed inside the proof. Its actual E-discard and ADE-relabel identities give the four copy entropy equalities. Existing CQ and product entropy prove zero CMI over AD. The eleven actual SSA inequalities then yield I(A:B)+I(A:CD)+3I(C:D|A)+I(C:D|B)-2I(C:D) at least zero.",
                Disp(Seq(D(0), Sp, Le, Sp, Call("Delta", Rho)))))));

    private static DocumentBlock Result(string id, string declaration, string title,
        string text, Formula formula) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
