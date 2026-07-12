using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class PdfWriterTests
{
    [Fact]
    public void QuestPdfWriterGeneratesEachPilotWithAPdfHeader()
    {
        foreach (var definition in DocumentDefinitions.All)
        {
            var pdf = QuestPdfWriter.Write(definition.Document);

            Assert.True(pdf.Length > 5);
            Assert.Equal("%PDF-", Encoding.ASCII.GetString(pdf.AsSpan()[..5]));
        }
    }
}
