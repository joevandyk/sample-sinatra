require File.dirname(__FILE__) + '/test_helper'

class TestSinatra < Test::Unit::TestCase
  include Rack::Test::Methods
  def app
    SinatraApp
  end

  def test_get
    get '/'
    assert last_response.ok?
    assert_equal({:result => Example.get_something}.to_json, last_response.body)
  end
end
