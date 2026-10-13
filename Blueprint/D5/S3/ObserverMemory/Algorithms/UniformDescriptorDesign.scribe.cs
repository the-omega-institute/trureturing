using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class UniformDescriptorDesignDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite common-descriptor design and budget syntax.",
        H("Finite common-descriptor design and budget syntax"),
        Blocks(
            Paragraph(Text("The descriptor tuple is selected before source quantification. Every source may have its own terminal epoch and phase witnesses. Shared compares all admitted sources at each common halt, across charts and across independently quantified terminal epochs. Feasibility is an intermediate native property and contains no assumption of solver correctness or installed outputs.")),
            Describe.Lean(DescribeId.Create("validformula"), Handle("ValidFormula"),
                H("Validity includes unreachable reads"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The conjunction checks every read occurrence and its fixed descriptor block. An unreachable read is not exempt. Empty read conjunctions are true."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("total"), Handle("Total"),
                H("Every admitted original source reaches a halt"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For each chart, universally quantify its complete source tuple, require admission, and take the finite disjunction of H over all halt controls. An empty halt list gives false inside each admitted implication. Empty source families remain vacuous."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shared"), Handle("Shared"),
                H("Two independent whole-source blocks"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The first tuple embeds in the left source block and the second tuple in a separate right block. Both H formulas share the outer descriptor tuple and bind separate terminal epochs. Admission is required for both sources before whole-row Same is interpreted."))),
                DescribeRole.Definition),
            Paragraph(Text("For a fixed halt, the original Reach query is the finite chart disjunction of exists n, Adm_eta(n) and H_eta,h(n;delta), with the common descriptor tuple held free. Empty charts give false. The installation's chartSource solves the admitted tuple and terminal epoch query, and sourceSearch uses List.findSome? over every chart. This directly supplies the UDB.18 query and its complete default branch without an additional unused formula declaration.")),
            Describe.Lean(DescribeId.Create("phi"), Handle("Phi"),
                H("One common descriptor choice"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The natural descriptor existential encloses Total, Shared and Valid, with no source-dependent descriptor choices. The result has Fin zero free coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("psi"), Handle("Psi"),
                H("The actual closed budget sentence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The finite fold ranges over candidates of every size one through K and every graph/type assignment. Each disjunct is Phi. This is an actual closed Presburger formula, built with explicit finite products and folds; no solver interface or decision assumption is present."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nativetotal"), Handle("NativeTotal"),
                H("Native eventuality on the original family"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every original source has its own finite native Run to a genuine halt. Epochs are unbounded and need not agree between sources."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nativeshared"), Handle("NativeShared"),
                H("Complete rows agree at every shared halt"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("All source pairs and all independently chosen halt epochs are quantified. This proves row constancy on each halt support. It does not assert that an arbitrary preloaded row equals that constant."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("valid-correct"), Handle("valid_correct"),
                H("Every occurrence has its exact validity predicate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The original finite validity fold is equivalent to Valid on the exact descriptor blocks. Formula.realize_relabel and the existing finite-fold semantics supply this consumed validity binding."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phi-correct"), Handle("phi_correct"),
                H("Native feasibility of the closed descriptor sentence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The original Phi sentence is equivalent to Feasible. The installation completeness proof directly consumes the original semantic bridge, including exact native support and the original source chart surjectivity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("design-correct"), Handle("design_correct"),
                H("Exact Valid Total and Shared semantics"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Validity has its exact local predicate semantics. Under a valid Real-compatible literal assignment, Total is equivalent to native halting for every original source and Shared is equivalent to complete-row constancy on every native shared halt support. The disjoint admitted chart bijection supplies every original source; Same is used only on two admitted tuples."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("feasible"), Handle("Feasible"),
                H("Native graph feasibility before extraction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("There is one valid numeric descriptor tuple whose supplied common realizations give native Total and Shared. No correct output or recovery conclusion is assumed. A later constructor must obtain a reaching admitted source, install its complete target row, and then use Shared."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("budget-correct"), Handle("budget_correct"),
                H("Exact bounded candidate feasibility"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Psi is true precisely when one complete typed candidate of a positive size at most K is Feasible. This closes finite arithmetic construction and its native semantic characterization. UniformDescriptorInstallation consumes this characterization to produce eager literals and complete rows, and to prove original successful-table necessity and task correspondence."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(Owner + name);
}
