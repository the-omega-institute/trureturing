using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;

internal sealed class BlindKernelObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonempty blind residual obstructs every finite or pointwise language extension.",
        H("Blind Kernel Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("blind-kernel-factorization-obstruction"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelObstruction."
                        + "blind_kernel_obstruction"),
                H("Blind residuals obstruct every package extension"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The package has a code type Gamma, a codomain family Dgamma, and a "
                            + "definition readout into Dgamma(code) for each code. The imported "
                            + "dependent jointKernel and jointReadout are reused directly. The blind "
                            + "residual is only the named intersection of jointKernel with the "
                            + "canonical defectRelation; no second kernel, joint readout, or "
                            + "target-defect relation is introduced.")),
                    Paragraph(Text(
                        "If the residual is empty, adjoining the full pointwise language to the "
                            + "baseline admits a target recovery factor. This uses the accepted "
                            + "target recovery criterion and the required inhabited-state "
                            + "hypothesis. The remaining exhaustive alternative is either a "
                            + "sufficient finite selection or the compactification condition: "
                            + "full pointwise factorization with no finite sufficient selection.")),
                    Paragraph(Text(
                        "If the residual contains a pair, the baseline and every package "
                            + "definition agree on that pair while the target differs. Hence no "
                            + "finite indexed selection and no arbitrary subpackage pointwise "
                            + "union admits a target factor map. Repeated indices add no readout "
                            + "information, so arbitrary indexed unions are represented by their "
                            + "subpackage of values.")),
                    Paragraph(Text(
                        "The proof applies the accepted target recovery criterion to each "
                            + "persisting canonical defect. Thus the obstruction is inherited "
                            + "from the repository factorization theorem rather than reproved."))),
                DescribeRole.Theorem))));

    private static Formula Extension(Formula baseline, Formula definitions) =>
        Call("languageExtension", baseline, definitions);

    private static Formula Residual(Formula definitions, Formula baseline, Formula target) =>
        Call("blindResidual", definitions, baseline, target);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula baselineType = F.Id("C");
        Formula targetType = F.Id("Target");
        Formula codeType = F.Id("Gamma");
        Formula codomain = F.Id("Dgamma");
        Formula type = F.Id("Type");
        Formula baseline = F.Id("q");
        Formula target = F.Id("T");
        Formula definitions = F.Id("definitions");
        Formula codes = F.Id("codes");
        Formula code = F.Id("code");
        Formula index = F.Id("i");
        Formula subpackage = F.Id("Delta");
        Formula n = F.Id("n");
        Formula recover = F.Id("recover");
        Formula residual = Residual(definitions, baseline, target);
        Formula finiteSelection =
            Call("finiteSelectionSufficient", definitions, baseline, target);
        Formula compactification =
            Call("compactificationRequired", definitions, baseline, target);
        Formula selectedDefinitions = Seq(
            Open, index, Sp, Mapsto, Sp,
            Call("apply", definitions, Call("apply", codes, index)), Close);
        Formula finiteValues = Call("Pi", Seq(
            index, Colon, Sp, Call("Fin", n), Comma, Sp,
            Call("apply", codomain, Call("apply", codes, index))));
        Formula finiteObstruction = Seq(
            Forall, Sp, n, Colon, Sp, F.Id("Nat"), Comma, Sp,
            codes, Colon, Sp, Arrow(Call("Fin", n), codeType), Comma, Esc,
            Neg, Exists, Sp, recover, Colon, Sp,
            Arrow(Call("Prod", baselineType, finiteValues), targetType), Comma, Esc,
            target, Sp, Eq, Sp,
            Call("comp", recover, Extension(baseline, selectedDefinitions)));
        Formula arbitraryDefinitions = Seq(
            Open, code, Sp, Mapsto, Sp,
            Call("apply", definitions, Call("val", code)), Close);
        Formula arbitraryValues = Call("Pi", Seq(
            code, Colon, Sp, subpackage, Comma, Sp,
            Call("apply", codomain, Call("val", code))));
        Formula arbitraryObstruction = Seq(
            Forall, Sp, subpackage, Colon, Sp, Call("Set", codeType), Comma, Esc,
            Neg, Exists, Sp, recover, Colon, Sp,
            Arrow(Call("Prod", baselineType, arbitraryValues), targetType), Comma, Esc,
            target, Sp, Eq, Sp,
            Call("comp", recover, Extension(baseline, arbitraryDefinitions)));
        Formula fullValues = Call("Pi", Seq(
            code, Colon, Sp, codeType, Comma, Sp,
            Call("apply", codomain, code)));
        Formula fullFactorization = Seq(
            Exists, Sp, recover, Colon, Sp,
            Arrow(Call("Prod", baselineType, fullValues), targetType), Comma, Esc,
            target, Sp, Eq, Sp,
            Call("comp", recover, Extension(baseline, definitions)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, baselineType, Comma, Sp,
            targetType, Comma, Sp, codeType, Colon, Sp, type, Comma, Esc,
            codomain, Colon, Sp, Arrow(codeType, type), Comma, Sp,
            OpenBracket, Call("Nonempty", state), CloseBracket, Comma, Sp,
            definitions, Colon, Sp, Call("Pi", Seq(
                code, Colon, Sp, codeType, Comma, Sp,
                Call("Concept", state, Call("apply", codomain, code)))), Comma, Sp,
            baseline, Colon, Sp, Call("Concept", state, baselineType), Comma, Sp,
            target, Colon, Sp, Call("Concept", state, targetType), Comma, Esc,
            Open, residual, Sp, Eq, Sp, Emptyset, Sp, Rightarrow, Sp,
            Open, fullFactorization, Close, Sp, Land, Sp,
            Open, finiteSelection, Sp, Lor, Sp, compactification, Close, Close,
            Sp, Land, RowBreak,
            Open, Call("Nonempty", residual), Sp, Rightarrow, Sp,
            Open, finiteObstruction, Close, Sp, Land, RowBreak, Grp(),
            Open, arbitraryObstruction, Close, Sp, Land, Sp,
            Neg, finiteSelection, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
