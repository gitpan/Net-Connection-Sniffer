use ExtUtils::MakeMaker;
use Config;
use lib qw(inc);

my $pkg = 'Net::Connection::Sniffer';
$pkg =~ /[^:]+$/;
my $module = $& .'.pm';

# See lib/ExtUtils/MakeMaker.pm for details of how to influence
# the contents of the Makefile that is written.

my %makeparms = (
    'NAME'		=> $pkg,
    'VERSION_FROM'	=> $module, # finds $VERSION
    'PREREQ_PM'		=> {
				Net::DNS::Codes		=> 0.09,
				Net::DNS::ToolKit	=> 0.41,
				Net::Interface		=> 1.008,
				Net::NBsocket		=> 0.14,
				Sys::Hostname::FQDN	=> 0.07,
				Proc::PidUtil		=> 0.08,
				NetAddr::IP		=> 4.024,
				Sys::Sig		=> 0.03,
			},
    'LIBS'		=> '-lpcap',
    'clean'		=> { FILES    => "*~ tmp* auto*"},
    'realclean'		=> { FILES    => "config.h config.log config.status"},
    'dist'		=> {COMPRESS=>'gzip', SUFFIX=>'gz'}
);

unless (-e './config.h') {
  system('./configure');
}

sub MY::top_targets {
  package MY;
  my $inherited = shift->SUPER::top_targets(@_);
  $inherited =~ s/(pure_all\s+::.+)/$1 README/;
  $inherited;
}

sub MY::post_constants {
  my $post_constants = q|
MY_POD2TEXT = |. $Config{scriptdirexp} .'/pod2text' .q|   
|;
} 

sub MY::postamble {
  package MY;
  my $postamble = q|
README  : |. $module .q|
	@$(MY_POD2TEXT) |. $module .q| > README

|;
}

WriteMakefile(%makeparms);

unless (open(F,'./config.h')) {
  warn "can not find ./config.h\n";
  exit;
}

unless (grep {/#define HAVE_PCAP/} (<F>)) {
  close F;
  warn "prerequisite 'libpcap' not found\n";
  exit;
}
close F;


