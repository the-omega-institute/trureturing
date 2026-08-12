using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class ScalingRegisterRigidityDocument : IScribeDocumentDefinition
{
    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);

    private static LeanDeclarationRef LeanInductive(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Inductive,
            requireNoSorry: true);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Typed realization carries analytic uniqueness through the registered action to conditional total-code rigidity.",
        H("Scaling-Register Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-scaling-register-is-a-nontrivial-coordinatewise-exponential"),
                DeclarationHandle.Create("D5/S3/Zeros/ScalingRegisterRigidity.ScalingRegister"),
                H("A scaling register is a nontrivial coordinatewise exponential"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a ledger length ell and factor family R, ScalingRegister(ell,R) "
                        + "means that some g gives R(s,a)=exp(g(s)ell(a)) for every s and a, "
                        + "and that R(s,a) differs from one at some coordinate. This is the "
                        + "formal carrier of Definition 23.2's dependence and nontriviality "
                        + "clauses.")),
                    Paragraph(Text(
                        "Honest scope declaration: the predicate does not internalize "
                        + "\"unrecorded\" ledger custody. Address independence is the formal "
                        + "proxy for an explicit global ledger factor; the institutional "
                        + "classification itself remains at the narrative layer."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a-nontrivial-register-is-not-address-independent"),
                DeclarationHandle.Create("D5/S3/Zeros/ScalingRegisterRigidity.scaling_register_not_address_independent"),
                H("A nontrivial register is not address-independent"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the zero address every exponential register equals one. Address "
                    + "independence would therefore make every coordinate one, contradicting "
                    + "the explicit nontrivial witness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-register-acts-on-the-tagged-data-field"),
                DeclarationHandle.Create("D5/S3/Zeros/ScalingRegisterRigidity.applyRegister"),
                H("A register acts on the tagged data field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For data X.data(a,s), applyRegister(R,X) replaces that value by "
                    + "R(s,a)X.data(a,s), while preserving the rules and ledger fields."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a-nontrivial-register-changes-nowhere-zero-data"),
                DeclarationHandle.Create("D5/S3/Zeros/ScalingRegisterRigidity.applyRegister_ne_of_nontrivial"),
                H("A nontrivial register changes nowhere-zero data"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the nontrivial witness, equality of total codes would equate the data "
                    + "values R(s,a)X.data(a,s) and X.data(a,s). Cancelling the explicitly "
                    + "nonzero data value forces R(s,a)=1, a contradiction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("realization-projects-object-data-and-carries-register-actions"),
                DeclarationHandle.Create("D5/S3/Zeros/ScalingRegisterRigidity.RealizesAt"),
                H("Realization projects object data and carries register actions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "RealizesAt(a,X,f) records both that the declared address projection of "
                    + "X.data reads as f and that the same projection sends applyRegister(R,X) "
                    + "to the pointwise product R(s,a)f(s). The compatibility clause is a "
                    + "defining model law, not a bridge assumption derived from mathlib."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("realized-same-germ-and-same-total-code-force-a-trivial-register"),
                DeclarationHandle.Create("D5/S3/Zeros/ScalingRegisterRigidity.realized_same_germ_same_total_code_forces_trivial_register"),
                H("Realized same germ and same total code force a trivial register"),
                StatementSource.FromAuthor(Disp(Seq(Begin, Grp(F.Id("gathered")), F.Id("U"), Subseteq, Mathbb, Grp(F.Id("C")), Comma, Esc, F.Id("f"), Comma, Widetilde, Sp, F.Id("f"), Colon, Mathbb, Grp(F.Id("C")), To, Mathbb, Grp(F.Id("C")), Comma, Quad, Sp, Operatorname, Grp(F.Id("AnalyticOnNhd")), Open, F.Id("f"), Comma, F.Id("U"), Close, Comma, Quad, Operatorname, Grp(F.Id("AnalyticOnNhd")), Open, Widetilde, Sp, F.Id("f"), Comma, F.Id("U"), Close, Comma, RowBreak, Operatorname, Grp(F.Id("IsPreconnected")), Open, F.Id("U"), Close, Comma, Quad, Sp, F.Id("s"), Underscore, D(0), InMacro, Sp, F.Id("U"), Comma, Esc, F.Id("f"), Eq, Underscore, Grp(Operatorname, Grp(F.Id("nhds")), Open, F.Id("s"), Underscore, D(0), Close), Widetilde, Sp, F.Id("f"), Comma, RowBreak, F.Id("R"), Colon, Mathbb, Grp(F.Id("C")), To, Sp, F.Id("A"), To, Mathbb, Grp(F.Id("C")), Comma, Quad, Sp, F.Id("X"), Colon, Operatorname, Grp(F.Id("TotalCode")), Open, F.Id("A"), To, Mathbb, Grp(F.Id("C")), To, Mathbb, Grp(F.Id("C")), Comma, F.Id("Q"), Comma, F.Id("L"), Close, Comma, RowBreak, Operatorname, Grp(F.Id("RealizesAt")), Open, F.Id("a"), Comma, F.Id("X"), Comma, F.Id("f"), Close, Comma, Quad, Operatorname, Grp(F.Id("RealizesAt")), Open, F.Id("a"), Comma, Operatorname, Grp(F.Id("applyRegister")), Open, F.Id("R"), Comma, F.Id("X"), Close, Comma, Widetilde, Sp, F.Id("f"), Close, Comma, RowBreak, Forall, Sp, F.Id("a"), Comma, F.Id("s"), Comma, Esc, F.Id("X"), Underscore, Grp(Operatorname, Grp(F.Id("data"))), Open, F.Id("a"), Comma, F.Id("s"), Close, Neq, D(0), Comma, Quad, Operatorname, Grp(F.Id("applyRegister")), Open, F.Id("R"), Comma, F.Id("X"), Close, Eq, F.Id("X"), End, Grp(F.Id("gathered")), Quad, Rightarrow, Quad, Left, Open, F.Id("f"), Eq, Widetilde, Sp, F.Id("f"), F.Text, Grp(Sp, F.Id("on"), Sp), F.Id("U"), Right, Close, Land, Left, Open, Forall, Sp, F.Id("s"), Comma, Esc, Widetilde, Sp, F.Id("f"), Open, F.Id("s"), Close, Eq, F.Id("R"), Open, F.Id("s"), Comma, F.Id("a"), Close, F.Id("f"), Open, F.Id("s"), Close, Right, Close, Land, Left, Open, Forall, Sp, F.Id("s"), Comma, F.Id("a"), Comma, Esc, F.Id("R"), Open, F.Id("s"), Comma, F.Id("a"), Close, Eq, D(1), Right, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Analytic continuation uniqueness identifies the two readings on U. The "
                        + "RealizesAt model law then identifies the registered reading pointwise "
                        + "with R(s,a)f(s). Finally, a non-one witness and nowhere-zero data would "
                        + "produce an applyRegister object change, contradicting equal total code.")),
                    Paragraph(Text(
                        "Honest scope declaration: this is conditional on the typed realization "
                        + "relations and does not internalize unrecorded ledger custody."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("realized-code-preserving-continuations-exclude-scaling-registers"),
                DeclarationHandle.Create("D5/S3/Zeros/ScalingRegisterRigidity.realized_same_germ_same_total_code_excludes_scaling_register"),
                H("Realized code-preserving continuations exclude scaling registers"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The realized rigidity theorem makes R pointwise one, contradicting the "
                    + "nontriviality witness required by ScalingRegister. This is the explicit "
                    + "ScalingRegister exclusion and retains every realization and code premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-scaling-register-predicate-has-a-concrete-witness"),
                DeclarationHandle.Create("D5/S3/Zeros/ScalingRegisterRigidity.integer_scaling_register_exists"),
                H("The scaling-register predicate has a concrete witness"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the integer ledger, the cast-to-real length and the factor exp(pi i n) "
                    + "satisfy the register shape, while n=1 evaluates to minus one rather than "
                    + "one. This kernel-checked counterexample-style witness prevents the main "
                    + "exclusion theorem from succeeding merely because ScalingRegister is empty."))),
                DescribeRole.Theorem)),
[
                        DocumentEdge.Dependency.Create(
                            GidRef.Create("D5/S0/Conventions/TotalCode")),
                        DocumentEdge.Dependency.Create(
                            GidRef.Create("D5/S3/Zeros/CompletedZeta")),
                    ]));
}
