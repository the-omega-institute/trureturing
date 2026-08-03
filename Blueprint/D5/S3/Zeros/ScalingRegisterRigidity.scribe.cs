using static StrataLint.Scribe.DefinitionDsl;

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

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Zeros/ScalingRegisterRigidity",
            "Typed realization carries analytic uniqueness through the registered action to conditional total-code rigidity."),
        H("Scaling-Register Rigidity"),
        Blocks(
            DocumentBlock.Describe.Definition(
                DescribeId.Create("a-scaling-register-is-a-nontrivial-coordinatewise-exponential"),
                H("A scaling register is a nontrivial coordinatewise exponential"),
                LeanDefinition(
                    "D5/S3/Zeros/ScalingRegisterRigidity.ScalingRegister"),
                DescribeProvenance.RepoDerived(),
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
                        + "classification itself remains at the narrative layer.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("a-nontrivial-register-is-not-address-independent"),
                H("A nontrivial register is not address-independent"),
                LeanTheorem(
                    "D5/S3/Zeros/ScalingRegisterRigidity.scaling_register_not_address_independent"),
                LatexStatement.Create(
                    @"$$\forall A\,[\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},"
                    + @"\ \forall R:\mathbb{C}\to A\to\mathbb{C},\ "
                    + @"\operatorname{ScalingRegister}(\ell,R)"
                    + @"\Rightarrow\neg\forall s,a,b,\ R(s,a)=R(s,b).$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "At the zero address every exponential register equals one. Address "
                    + "independence would therefore make every coordinate one, contradicting "
                    + "the explicit nontrivial witness.")))
            ),
            DocumentBlock.Describe.Definition(
                DescribeId.Create("a-register-acts-on-the-tagged-data-field"),
                H("A register acts on the tagged data field"),
                LeanDefinition(
                    "D5/S3/Zeros/ScalingRegisterRigidity.applyRegister"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For data X.data(a,s), applyRegister(R,X) replaces that value by "
                    + "R(s,a)X.data(a,s), while preserving the rules and ledger fields.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("a-nontrivial-register-changes-nowhere-zero-data"),
                H("A nontrivial register changes nowhere-zero data"),
                LeanTheorem(
                    "D5/S3/Zeros/ScalingRegisterRigidity.applyRegister_ne_of_nontrivial"),
                LatexStatement.Create(
                    @"$$\left(\forall a,s,\ X_{\operatorname{data}}(a,s)\neq0\right)\land"
                    + @"\left(\exists s,a,\ R(s,a)\neq1\right)\Rightarrow"
                    + @"\operatorname{applyRegister}(R,X)\neq X.$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "At the nontrivial witness, equality of total codes would equate the data "
                    + "values R(s,a)X.data(a,s) and X.data(a,s). Cancelling the explicitly "
                    + "nonzero data value forces R(s,a)=1, a contradiction.")))
            ),
            DocumentBlock.Describe.Definition(
                DescribeId.Create("realization-projects-object-data-and-carries-register-actions"),
                H("Realization projects object data and carries register actions"),
                LeanInductive(
                    "D5/S3/Zeros/ScalingRegisterRigidity.RealizesAt"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "RealizesAt(a,X,f) records both that the declared address projection of "
                    + "X.data reads as f and that the same projection sends applyRegister(R,X) "
                    + "to the pointwise product R(s,a)f(s). The compatibility clause is a "
                    + "defining model law, not a bridge assumption derived from mathlib.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("realized-same-germ-and-same-total-code-force-a-trivial-register"),
                H("Realized same germ and same total code force a trivial register"),
                LeanTheorem(
                    "D5/S3/Zeros/ScalingRegisterRigidity.realized_same_germ_same_total_code_forces_trivial_register"),
                LatexStatement.Create(
                    @"$$\begin{gathered}U\subseteq\mathbb{C},\ f,\widetilde f:\mathbb{C}\to\mathbb{C},"
                    + @"\quad \operatorname{AnalyticOnNhd}(f,U),\quad"
                    + @"\operatorname{AnalyticOnNhd}(\widetilde f,U),\\"
                    + @"\operatorname{IsPreconnected}(U),\quad s_0\in U,\ "
                    + @"f=_{\operatorname{nhds}(s_0)}\widetilde f,\\"
                    + @"R:\mathbb{C}\to A\to\mathbb{C},\quad "
                    + @"X:\operatorname{TotalCode}(A\to\mathbb{C}\to\mathbb{C},Q,L),\\"
                    + @"\operatorname{RealizesAt}(a,X,f),\quad"
                    + @"\operatorname{RealizesAt}(a,\operatorname{applyRegister}(R,X),\widetilde f),\\"
                    + @"\forall a,s,\ X_{\operatorname{data}}(a,s)\neq0,\quad"
                    + @"\operatorname{applyRegister}(R,X)=X"
                    + @"\end{gathered}\quad\Rightarrow\quad"
                    + @"\left(f=\widetilde f\text{ on }U\right)\land"
                    + @"\left(\forall s,\ \widetilde f(s)=R(s,a)f(s)\right)\land"
                    + @"\left(\forall s,a,\ R(s,a)=1\right).$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Analytic continuation uniqueness identifies the two readings on U. The "
                        + "RealizesAt model law then identifies the registered reading pointwise "
                        + "with R(s,a)f(s). Finally, a non-one witness and nowhere-zero data would "
                        + "produce an applyRegister object change, contradicting equal total code.")),
                    Paragraph(Text(
                        "Honest scope declaration: this is conditional on the typed realization "
                        + "relations and does not internalize unrecorded ledger custody.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("realized-code-preserving-continuations-exclude-scaling-registers"),
                H("Realized code-preserving continuations exclude scaling registers"),
                LeanTheorem(
                    "D5/S3/Zeros/ScalingRegisterRigidity.realized_same_germ_same_total_code_excludes_scaling_register"),
                LatexStatement.Create(
                    @"$$\operatorname{RealizesAt}(a,X,f)\land"
                    + @"\operatorname{RealizesAt}(a,\operatorname{applyRegister}(R,X),\widetilde f)"
                    + @"\land\text{ same germ}\land\text{ same total code}"
                    + @"\Rightarrow\neg\operatorname{ScalingRegister}(\ell,R).$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The realized rigidity theorem makes R pointwise one, contradicting the "
                    + "nontriviality witness required by ScalingRegister. This is the explicit "
                    + "ScalingRegister exclusion and retains every realization and code premise.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-scaling-register-predicate-has-a-concrete-witness"),
                H("The scaling-register predicate has a concrete witness"),
                LeanTheorem(
                    "D5/S3/Zeros/ScalingRegisterRigidity.integer_scaling_register_exists"),
                LatexStatement.Create(
                    @"$$\operatorname{ScalingRegister}\!\left(\operatorname{castAddHom}_{\mathbb{R}},"
                    + @"\ (s,n)\mapsto\exp(\pi i n)\right).$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "On the integer ledger, the cast-to-real length and the factor exp(pi i n) "
                    + "satisfy the register shape, while n=1 evaluates to minus one rather than "
                    + "one. This kernel-checked counterexample-style witness prevents the main "
                    + "exclusion theorem from succeeding merely because ScalingRegister is empty.")))
            ))));
}
