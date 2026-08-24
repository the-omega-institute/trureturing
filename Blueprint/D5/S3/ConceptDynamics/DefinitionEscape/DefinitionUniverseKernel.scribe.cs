using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;

internal sealed class DefinitionUniverseKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula x = F.Id("X");
        Formula y = F.Id("Y");
        Formula s = F.Id("S");
        Formula d = F.Id("d");
        Formula e = F.Id("e");
        Formula codomain = F.Id("D");
        Formula universe = F.Id("U");
        Formula defX = Call("Def", x);
        Formula defY = Call("Def", y);
        Formula kernelD = Call("ker", d);
        Formula kernelE = Call("ker", e);
        Formula imageD = Call("Im", d);
        Formula refinesDE = Call("DefinitionRefines", d, e);
        Formula refinesED = Call("DefinitionRefines", e, d);
        Formula equivalent = Call("DefinitionEquivalent", d, e);
        Formula sigmaPackage = Seq(
            Sigma, Underscore, Grp(codomain, Colon, Sp, universe), Sp,
            Arrow(x, codomain));
        Formula methodInput = Seq(
            Call("DState", x), Sp, Times, Sp, Call("Residual", x));
        Formula statement = Disp(Seq(
            Call("Def", x), Sp, Eq, Sp, sigmaPackage, Comma, RowBreak, Grp(),
            kernelD, Sp, Eq, Sp, Call("SetoidKer", d), Comma, Sp,
            imageD, Sp, Eq, Sp, Call("range", d), Comma, RowBreak, Grp(),
            equivalent, Sp, Leftrightarrow, Sp, kernelD, Sp, Eq, Sp, kernelE,
            Comma, Sp, refinesDE, Sp, Leftrightarrow, Sp,
            kernelE, Sp, Subseteq, Sp, kernelD, Comma, RowBreak, Grp(),
            equivalent, Sp, Leftrightarrow, Sp, Open, refinesDE, Sp, Land, Sp,
            refinesED, Close, Comma, Sp,
            Open, imageD, Sp, Eq, Sp, Mathrm, Grp(F.Id("univ")), Close,
            Sp, Leftrightarrow, Sp, Call("Surjective", d), Comma, RowBreak, Grp(),
            Call("MetaDef", x), Sp, Eq, Sp, Call("Def", defX), Comma, Sp,
            Call("Generator", x, s), Sp, Eq, Sp, Arrow(s, defX), Comma,
            RowBreak, Grp(), Call("Transformer", x, y), Sp, Eq, Sp,
            Arrow(defX, defY), Comma, Sp, Call("Method", x), Sp, Eq, Sp,
            Arrow(methodInput, defX), Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Definitions form a dependent universe ordered by their equality kernels.",
            H("Definition Universe and Kernel Order"),
            Blocks(Describe.Lean(
                DescribeId.Create("definition-universe-kernel-specification"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscape/DefinitionUniverseKernel."
                        + "definition_universe_kernel"),
                H("The definition universe carries its kernel and higher-order constructors"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A definition on X is a dependent pair: its first projection is a "
                            + "codomain in the same universe and its second projection is the "
                            + "canonical Concept readout from X. Its kernel is delegated to "
                            + "Setoid.ker and its realized image to Set.range.")),
                    Paragraph(Text(
                        "Conceptual equivalence is literal equality of source kernels. The "
                            + "coarse-to-fine relation reverses kernel inclusion, so equality "
                            + "holds exactly when both directed refinements hold. The realized "
                            + "image is universal exactly when the packaged readout is surjective.")),
                    Paragraph(Text(
                        "MetaDef applies the same Sigma construction to Def X. Generators are "
                            + "S-indexed families, transformers map one definition universe to "
                            + "another, and a method consumes the paired definition and residual "
                            + "states to choose the next packaged definition.")),
                    Paragraph(Text(
                        "The repository's Refines relation is factorization rather than raw "
                            + "kernel inclusion. Separate bridge declarations apply the accepted "
                            + "concept-kernel order duality only for surjective readouts, where "
                            + "the two notions coincide. Boolean examples witness both a proper "
                            + "refinement and a realized image that omits a coordinate."))),
                DescribeRole.Theorem))));
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

}
