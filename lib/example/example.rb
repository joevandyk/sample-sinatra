require 'json'
module Example
  def self.get_something
    content_type :json
    { :result => 'success', :params => params }.to_json
  end
end
