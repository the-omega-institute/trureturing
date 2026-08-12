using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class AdditivePricingPruningDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite complete contexts preserve additive Born totals exactly, while one explicit " +
        "qutrit state and two complete contexts separate the corresponding quartic and sextic totals.",
        H("Exact Additive Pricing and Higher-Degree Pruning"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("additive-totals-are-context-invariant"),
                DeclarationHandle.Create("D5/S3/QuantumContext/AdditivePricingPruning.additive_total_context_invariant"),
                H("Additive totals are context-invariant"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("trace")), Open, Rho, Close,
                    Sp, Eq, Sp, D(1), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Complete")), Open, F.Id("C"), Close,
                    Sp, Rightarrow, Sp,
                    F.Id("T"), Underscore, Grp(D(2)), Open, Rho, Comma, Sp, F.Id("C"), Close,
                    Sp, Eq, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite matrix dimension and finite context, if the context resolves " +
                    "the identity and the priced matrix has trace one, then its additive Born total " +
                    "is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-finite-harmonic-pruning-certificate"),
                DeclarationHandle.Create("D5/S3/QuantumContext/AdditivePricingPruning.harmonic_spectral_pruning_certificate"),
                H("Exact finite harmonic pruning certificate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open,
                    F.Id("T"), Underscore, Grp(D(2)), Open, Rho, Comma, Sp,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("std"))), Close,
                    Sp, Eq, Sp, D(1), Sp, Land, Sp,
                    F.Id("T"), Underscore, Grp(D(2)), Open, Rho, Comma, Sp,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("aligned"))), Close,
                    Sp, Eq, Sp, D(1), Close,
                    Sp, Land, Sp, Open,
                    F.Id("T"), Underscore, Grp(D(4)), Open, Rho, Comma, Sp,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("std"))), Close,
                    Sp, Eq, Sp, Frac, Grp(D(1)), Grp(D(3)), Sp, Land, Sp,
                    F.Id("T"), Underscore, Grp(D(4)), Open, Rho, Comma, Sp,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("aligned"))), Close,
                    Sp, Eq, Sp, D(1), Close,
                    Sp, Land, Sp, Open,
                    F.Id("T"), Underscore, Grp(D(6)), Open, Rho, Comma, Sp,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("std"))), Close,
                    Sp, Eq, Sp, Frac, Grp(D(1)), Grp(D(9)), Sp, Land, Sp,
                    F.Id("T"), Underscore, Grp(D(6)), Open, Rho, Comma, Sp,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("aligned"))), Close,
                    Sp, Eq, Sp, D(1), Close,
                    Sp, Land, Sp,
                    F.Id("T"), Underscore, Grp(D(4)), Open, Rho, Comma, Sp,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("std"))), Close,
                    Sp, Lt, Sp,
                    F.Id("T"), Underscore, Grp(D(4)), Open, Rho, Comma, Sp,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("aligned"))), Close,
                    Sp, Land, Sp,
                    F.Id("T"), Underscore, Grp(D(6)), Open, Rho, Comma, Sp,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("std"))), Close,
                    Sp, Lt, Sp,
                    F.Id("T"), Underscore, Grp(D(6)), Open, Rho, Comma, Sp,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("aligned"))), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the equal-amplitude qutrit state, the additive totals in the standard and " +
                    "aligned contexts are both one. Their quartic totals are respectively one third " +
                    "and one, and their sextic totals are respectively one ninth and one. Both " +
                    "higher-degree comparisons are strict."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-born-controls-satisfy-the-numerical-tolerance"),
                DeclarationHandle.Create("D5/S3/QuantumContext/AdditivePricingPruning.born_control_numerical_tolerance_certificate"),
                H("Exact Born controls satisfy the numerical tolerance"),
                StatementSource.FromAuthor(Disp(Seq(
                    Vert, Re, Open,
                    F.Id("T"), Underscore, Grp(D(2)), Open, Rho, Comma, Sp,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("std"))), Close,
                    Close, Minus, D(1), Vert,
                    Sp, Eq, Sp, D(0),
                    Sp, Land, Sp,
                    Vert, Re, Open,
                    F.Id("T"), Underscore, Grp(D(2)), Open, Rho, Comma, Sp,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("aligned"))), Close,
                    Close, Minus, D(1), Vert,
                    Sp, Eq, Sp, D(0),
                    Sp, Land, Sp,
                    Frac, Grp(D(1)), Grp(D(1), D(0), Caret, Grp(D(1), D(6))),
                    Sp, Lt, Sp, Vert, Sp,
                    F.Id("T"), Underscore, Grp(D(4)), Open, Rho, Comma, Sp,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("std"))), Close,
                    Minus, Sp,
                    F.Id("T"), Underscore, Grp(D(4)), Open, Rho, Comma, Sp,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("aligned"))), Close, Vert))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The absolute additive-total defects in both contexts equal zero, and the " +
                    "quartic gap is strictly larger than 10^-16. In particular, both controls " +
                    "lie strictly within the stated tolerance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-certificate-is-inhabited-and-discriminating"),
                DeclarationHandle.Create("D5/S3/QuantumContext/AdditivePricingPruning.additive_pricing_anti_vacuity_witness"),
                H("The certificate is inhabited and discriminating"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, Rho, Comma, Sp,
                    Operatorname, Grp(F.Id("Positive")), Open, Rho, Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("trace")), Open, Rho, Close,
                    Sp, Eq, Sp, D(1), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Complete")), Open,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("std"))), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Complete")), Open,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("aligned"))), Close,
                    Sp, Land, Sp, D(0), Sp, Lt, Sp, Re, Open,
                    F.Id("T"), Underscore, Grp(D(2)), Open, Rho, Comma, Sp,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("std"))), Close, Close,
                    Sp, Land, Sp,
                    F.Id("T"), Underscore, Grp(D(4)), Open, Rho, Comma, Sp,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("std"))), Close,
                    Sp, Lt, Sp,
                    F.Id("T"), Underscore, Grp(D(4)), Open, Rho, Comma, Sp,
                    F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("aligned"))), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The imported equal-amplitude density matrix supplies positivity and trace " +
                        "one, while both displayed contexts supply exact identity resolutions.")),
                    Paragraph(Text(
                        "Its standard additive total is positive and its quartic standard total is " +
                        "strictly smaller than its quartic aligned total, so the certificate is " +
                        "inhabited and discriminating.")),
                    Paragraph(Text(
                        "The exact finite result asserts no random-basis sample variance, distribution " +
                        "over contexts, or general extremal classification."))),
                DescribeRole.Theorem))));
}
