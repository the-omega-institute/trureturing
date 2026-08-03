namespace StrataLint.Scribe.Tests;

public sealed class DescribeContractGoldenTests
{
    [Fact]
    public void RecurrenceAndMidlineDocumentsCarryExactDescribeContracts()
    {
        (string Gid, string Declaration, string Latex)[] expected =
        [
            (
                "D5/S1/Recurrence/CyclicNearestReturn",
                "D5/S1/Recurrence/CyclicNearestReturn.cyclic_nearest_return_spec",
                @"$$\forall \alpha\ [\operatorname{LinearOrder}(\alpha)]\ "
                + @"[\operatorname{DecidableEq}(\alpha)],\ "
                + @"\forall S\subseteq\alpha\ \text{finite},\ S\neq\emptyset:\ "
                + @"(\forall x\in S,\ \operatorname{succ}_S(x)\in S)\ \land\ "
                + @"(\forall x\in S,\ \operatorname{pred}_S(x)\in S)\ \land\ "
                + @"(\forall x\in S,\ \operatorname{pred}_S(\operatorname{succ}_S(x))=x)"
                + @"\ \land\ (\forall x\in S,\ "
                + @"\operatorname{succ}_S(\operatorname{pred}_S(x))=x)\ \land\ "
                + @"(\forall x,y\in S,\ x<y\Rightarrow\neg\,"
                + @"(y<\operatorname{succ}_S(x)))\ \land\ (\forall x,y\in S,\ "
                + @"y<x\Rightarrow\neg\,(\operatorname{pred}_S(x)<y))\ \land\ "
                + @"\operatorname{succ}_S(\max S)=\min S\ \land\ "
                + @"\operatorname{pred}_S(\min S)=\max S$$"),
            (
                "D5/S1/Recurrence/CyclicGapsPartition",
                "D5/S1/Recurrence/CyclicGapsPartition.cyclic_gaps_partition_circle",
                @"$$\forall S\subseteq[0,1)\ \text{finite},\ S\neq\emptyset,\ "
                + @"(\forall x\in\mathbb{R},\ g_S(x)="
                + @"\begin{cases}(1-x)+\min S,&x=\max S\\"
                + @"\operatorname{succ}_S(x)-x,&x\neq\max S\end{cases}):\ "
                + @"(\forall x\in S,\ \operatorname{succ}_S(x)\in S)\ \land\ "
                + @"(\forall x\in S,\ g_S(x)>0)\ \land\ "
                + @"\sum_{x\in S}g_S(x)=1$$"),
            (
                "D5/S3/Midline/OffLineScaling",
                "D5/S3/Midline/OffLineScaling.off_line_scaling_ledger_growth",
                @"$$\forall A\ [\operatorname{AddMonoid}(A)],\ "
                + @"\forall \ell:A\to_{+}\mathbb{R},\ \forall s\in\mathbb{C},\ "
                + @"\Re(s)\neq\frac{1}{2}\ \Rightarrow\ "
                + @"(\forall a\in A,\ 0<\ell(a)\Rightarrow"
                + @"\operatorname{scalingLedger}(\ell,s,a)\neq 0)\ \land\ "
                + @"(\forall a,b\in A,\ 0<\ell(a)\Rightarrow 0<\ell(b)\Rightarrow "
                + @"(0<\operatorname{scalingLedger}(\ell,s,a)\Leftrightarrow "
                + @"0<\operatorname{scalingLedger}(\ell,s,b)))\ \land\ "
                + @"(\forall a\in A,\ \forall m\in\mathbb{N},\ "
                + @"\operatorname{scalingLedger}(\ell,s,m\cdot a)="
                + @"m\operatorname{scalingLedger}(\ell,s,a))\ \land\ "
                + @"(\forall a\in A,\ 0<\ell(a)\Rightarrow\forall C\in\mathbb{R},\ "
                + @"\exists m\in\mathbb{N},\ C<\lvert\operatorname{scalingLedger}"
                + @"(\ell,s,m\cdot a)\rvert)$$"),
        ];

        var documents = DocumentDefinitions.All.ToDictionary(
            static item => item.Document.Header.Gid.Value,
            StringComparer.Ordinal);

        foreach (var item in expected)
        {
            var describe = Assert.Single(
                documents[item.Gid].Document.Content.Items.OfType<DocumentBlock.Describe>());
            var statement = Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement);

            Assert.Equal(DescribeKind.Theorem, describe.Kind);
            Assert.Equal(item.Declaration, statement.Value.Value);
            Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);
            Assert.Equal(item.Latex, describe.StatementLatex?.Value);
        }
    }
}
