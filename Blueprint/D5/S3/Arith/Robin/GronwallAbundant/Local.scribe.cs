using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.GronwallAbundant;

internal sealed class LocalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-deletion constraints, missing-prime mass and finite-code entropy for proper GA1 integers.",
        H("Local"),
        Blocks(
            Paragraph(Text("The source defines composite GA1 integers by all prime-deletion comparisons of the Gronwall quotient. Properness means at least three prime factors with multiplicity. Its section 8 gives Q1(x) at most exp(c*log(x)/log(log(x))) for some positive c and asks for an improvement.")),
            Describe.Remark(DescribeId.Create("source-counting-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Local.Q1"),
                H("The counting estimate and improvement question in section eight"),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Arith/caveney2012sacaga")),
                Blocks(Paragraph(Text("Section 8 states Q1(x) <= exp(c*log(x)/log(log(x))) for some positive c and suggests improving the estimate by counting good divisors. This cited estimate is distinct from the stronger upper bound proved here.")))),
            Describe.Lean(DescribeId.Create("gronwallq"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Local.gronwallQ"), H("The Gronwall quotient with its unmodified natural-logarithm denominator."),
                StatementSource.FromAuthor(QuotientFormula()), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Arith/caveney2012sacaga")),
                Blocks(Paragraph(Text("The Gronwall quotient with its unmodified natural-logarithm denominator."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("isga1"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Local.IsGA1"), H("A composite integer whose Gronwall quotient does not increase on deleting a prime."),
                StatementSource.FromAuthor(GAFormula()), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Arith/caveney2012sacaga")),
                Blocks(Paragraph(Text("A composite integer whose Gronwall quotient does not increase on deleting a prime."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("isproperga1"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Local.IsProperGA1"), H("Proper GA1 integers have at least three prime factors with multiplicity."),
                StatementSource.FromAuthor(ProperFormula()), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Arith/caveney2012sacaga")),
                Blocks(Paragraph(Text("Proper GA1 integers have at least three prime factors with multiplicity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("q1"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Local.Q1"), H("The number of proper GA1 integers at most a real cutoff."),
                StatementSource.FromAuthor(CountFormula()), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Arith/caveney2012sacaga")),
                Blocks(Paragraph(Text("The number of proper GA1 integers at most a real cutoff."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("proper-div-ge-four"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Local.proper_div_ge_four"), H("Deleting a prime from a proper GA1 integer leaves an integer at least four."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Deleting a prime from a proper GA1 integer leaves an integer at least four."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("proper-loglog-div-pos"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Local.proper_loglog_div_pos"), H("The iterated logarithm after deleting a prime from a proper GA1 integer is positive."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The iterated logarithm after deleting a prime from a proper GA1 integer is positive."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primedeletionsum"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Local.primeDeletionSum"), H("The finite geometric sum attached to the complete exponent of a prime."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite geometric sum attached to the complete exponent of a prime."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ga1-local-criterion"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Local.ga1_local_criterion"), H("The exact local comparison before changing logarithmic coordinates."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact local comparison before changing logarithmic coordinates."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prime-deletion-log-gap"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Local.prime_deletion_log_gap"), H("Concavity of the logarithm charges deletion by at least its relative log-size."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Concavity of the logarithm charges deletion by at least its relative log-size."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ga1-prime-power-log-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Local.ga1_prime_power_log_bound"), H("The GA1 comparison bounds every full local geometric sum."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The GA1 comparison bounds every full local geometric sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ga1-prime-power-le"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Local.ga1_prime_power_le"), H("Every prime-power divisor obeys the GA1 logarithmic barrier."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Arith/caveney2012sacaga")),
                Blocks(Paragraph(Text("CNS Theorem 9, section 6.1, printed pages 20-21: Every prime-power divisor obeys the GA1 logarithmic barrier."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prime-le-log"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Local.prime_le_log"), H("Every prime factor is at most the natural logarithm of a proper GA1 integer."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Arith/caveney2012sacaga")),
                Blocks(Paragraph(Text("CNS Theorem 9, section 6.1, printed pages 20-21: Every prime factor is at most the natural logarithm of a proper GA1 integer."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("square-le-two-log"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Local.square_le_two_log"), H("Repeated prime factors lie below the square-root cutoff."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Arith/caveney2012sacaga")),
                Blocks(Paragraph(Text("CNS Theorem 9, section 6.1, printed pages 20-21: Repeated prime factors lie below the square-root cutoff."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("proper-log-gt-two"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Local.proper_log_gt_two"), H("A proper GA1 integer has logarithm strictly greater than two."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A proper GA1 integer has logarithm strictly greater than two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("proper-log-ge-two"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Local.proper_log_ge_two"), H("The non-strict logarithmic threshold used in common GA1 budgets."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The non-strict logarithmic threshold used in common GA1 budgets."))), DescribeRole.Theorem))));

    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Seq(Operatorname, Grp(F.Id(n))), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, F.Id(n), Colon, Sp, t, Comma, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iffn(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula G(Formula n) => Call("G", n);
    private static Formula QuotientFormula()
    {
        var n=F.Id("n");
        return Disp(All("n", NatType(), Eqn(G(n), new Formula.Fraction(Call("sigma",D(1),n),
            Mul(n, Call("log",Call("log",n)))))));
    }
    private static Formula GAFormula()
    {
        var n=F.Id("N"); var p=F.Id("p");
        var factors=new Formula.Relation(p,FormulaRelationOperator.MemberOf,Call("primeFactors",n));
        var deletions=All("p",NatType(),Imp(factors,Le(G(Call("natdiv",n,p)),G(n))));
        return Disp(All("N",NatType(),Iffn(Call("IsGAone",n),
            And(Seq(Neg,Sp,Call("Prime",n)),And(Lt(D(1),n),deletions)))));
    }
    private static Formula ProperFormula()
    {
        var n=F.Id("N");
        return Disp(All("N",NatType(),Iffn(Call("IsProperGAone",n),
            And(Call("IsGAone",n),Le(D(3),Call("Omega",n))))));
    }
    private static Formula CountFormula()
    {
        var x=F.Id("x");
        return Disp(All("x",RealType(),Eqn(new Formula.Apply(new Formula.Subscript(F.Id("Q"),D(1)),[x]),
            Call("card",Call("filter",Seq(Operatorname,Grp(F.Id("IsProperGAone"))),
                Call("range",Add(Call("floorpos",x),D(1))))))));
    }
}
