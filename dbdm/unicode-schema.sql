CREATE TABLE unicode (
  codepoint character varying(6) PRIMARY KEY,
  charname text NOT NULL,
  category character(2) NOT NULL,
  combining integer NOT NULL,
  bidi character varying(3) NOT NULL,
  decomposition text,
  "decimal" integer,
  digit integer,
  "numeric" text,
  mirrored character(1) NOT NULL,
  oldname text,
  comment text,
  uppercase character varying(6) REFERENCES unicode(codepoint),
  lowercase character varying(6) REFERENCES unicode(codepoint),
  titlecase character varying(6) REFERENCES unicode(codepoint)
);

CREATE INDEX ON unicode(charname);

CREATE INDEX ON unicode(numeric);

\copy unicode FROM UnicodeData.txt DELIMITER ';' NULL ''
