using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIISLnUnipotentCommutatorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn Unipotent Commutators.",
        H("Type-A SLn Unipotent Commutators"),
        Blocks(
            Paragraph(Text("An elementary type-A step toward PartII Section5 class product width. Every actual upper unitriangular matrix, embedded with an equally sized auxiliary block, is a product of THREE actual commutators. The first two solve the odd/even adjacent entries by rectangular block multiplication; the third consumes the full proper-matrix reconstruction (13). No commutator-width, conjugacy-width, simplicity or field-size premise.")),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentcommutators-doubleembed"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIISLnUnipotentCommutators.doubleEmbed"),
                H("doubleEmbed"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Genuine embedding with an auxiliary block of the same size."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentcommutators-lowerblock"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIISLnUnipotentCommutators.lowerBlock"),
                H("Lower block shear"), StatementSource.FromAuthor(LowerBlockFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every field F in an arbitrary universe u, natural dimension n and square matrix A over F, lowerBlock(A) is the special linear matrix with identity diagonal blocks, zero upper right block and lower left block A; val denotes its underlying matrix, fromBlocks assembles the four displayed blocks, and det(val(lowerBlock(A))) is one, including when n is zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentcommutators-actual-upper-double-three-commutators"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIISLnUnipotentCommutators.actual_upper_double_three_commutators"),
                H("actual upper double three commutators"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two rectangular witnesses realize the complete matching strip, including all entries, rather than just its leading coordinates. -/ private theorem matching_commutator (p : ℕ) (x : Fin n → F) : (upperBlock (colourDiagonal (F:=F) p))⁻¹* (lowerBlock (colourStrip p x))⁻¹* upperBlock (colourDiagonal p)*lowerBlock (colourStrip p x)= doubleEmbed (stripUnit 1 (by decide) (fun i => if i.val%2=p then x i else 0)) := by rw [upper_inverse,lower_inverse] apply Subtype.ext change (fromBlocks (1:Matrix (Fin n) (Fin n) F) (-colourDiagonal p) 0 1)* (fromBlocks 1 0 (-colourStrip p x) 1)* (fromBlocks 1 (colourDiagonal p) 0 1)* (fromBlocks 1 0 (colourStrip p x) 1)= fromBlocks (1+colourStrip p x) 0 0 1 simp [fromBlocks_multiply,add_mul,mul_add,diagonal_strip,strip_diagonal] private theorem unit_product (a b : SpecialLinearGroup (Fin n) F) (ha : LayerDepth 1 (a.val-1)) (hb : LayerDepth 1 (b.val-1)) : LayerDepth 1 ((a*b).val-1) := by have he : (a*b).val-1=(a.val-1)*(b.val-1)+(a.val-1)+(b.val-1) := by rw [SpecialLinearGroup.coe_mul]; noncomm_ring rw [he] exact (unitLayer% depth_add) ((unitLayer% depth_add) ((unitLayer% depth_mono) ((unitLayer% depth_mul) ha hb) (by decide)) ha) hb private theorem strip_depth1 (x : Fin n → F) : LayerDepth 1 ((stripUnit 1 (by decide) x).val-1) := by simpa only [stripUnit,add_sub_cancel_left] using (unitLayer% strip_depth) 1 x /-- EVERY upper unitriangular target, every field and rank (including 0/1), is reconstructed with three ordered commutators in the actual double-sized special linear group. Witnesses depend on the target; the auxiliary block and the number THREE do not."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
    private static Formula LowerBlockFormula()
    {
        Formula field = F.Id("F"), n = F.Id("n"), a = F.Id("A");
        Formula fin = Call("Fin", n);
        Formula matrix = Call("Matrix", fin, fin, field);
        Formula value = Call("val", Call("lowerBlock", a));
        Formula body = new Formula.Logic(
            new Formula.Relation(value, FormulaRelationOperator.Equal,
                Call("fromBlocks", F.D(1), F.D(0), a, F.D(1))),
            FormulaLogicOperator.And,
            new Formula.Relation(Call("det", value), FormulaRelationOperator.Equal, F.D(1)));
        return F.Disp(F.Seq(F.Forall, F.Sp, F.Id("u"), F.Comma, F.Sp,
            All("F", F.Seq(F.Operatorname, F.Grp(F.Id("Type")), F.Sp, F.Id("u")),
                new Formula.Logic(Call("Field", field), FormulaLogicOperator.Implies,
                    All("n", F.Seq(F.Mathbb, F.Grp(F.Id("N"))), All("A", matrix, body))))));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
